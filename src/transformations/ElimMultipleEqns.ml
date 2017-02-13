
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Merge Multiple Equations into One} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst
module T = TI.Default
module U = T.U
module P = T.P
module PStmt = Statement.Print(P)(P)
module Pat = Pattern.Make(T)
module Red = Reduce.Make(T)
module TyMo = TypeMono.Make(T)

type ty = T.t
type term = T.t
type env = (term,ty) Env.t

let name = "elim_multi_eqns"
let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg ->
        Some (Utils.err_sprintf "@[<2>elimination of multiple equations:@ %s@]" msg)
      | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

type pattern =
  | P_term of term  (* should be a pattern, we will see *)
  | P_any (* no pattern, always succeeds *)

type path_cell = {
  path_var: ty Var.t;
  path_pat: pattern;
}

type local_state = {
  root: term; (* term being pattern matched on (used in "undefined" cases) *)
  path: path_cell list; (* current "path" in the matching *)
  offset: int; (* for fresh variables *)
  env: env;
}

type ('a, 'b, 'ty) decision_node =
  | DN_match of ('a, 'b, 'ty) decision_node_match
  | DN_if of 'b list * 'b list  (* true/false *)
  | DN_bind of 'b list (* only accepts variables *)

and ('a, 'b, 'ty) decision_node_match = {
  dn_data_ty: term Stmt.data_type; (* all constructors required *)
  dn_by_cstor: 'a list ID.Map.t; (* cstor -> sub-list of cases *)
  dn_wildcard: 'b list; (* matching anything *)
}

let pp_pat out = function
  | P_any -> Format.fprintf out "_"
  | P_term t -> P.pp out t

let pp_path_cell out c : unit =
  Format.fprintf out "{@[%a =?= %a@]}"
    Var.pp c.path_var pp_pat c.path_pat

let pp_path out p =
  Format.fprintf out "[@[<hv>%a@]]"
    (Utils.pp_list ~sep:"," pp_path_cell) (List.rev p)

let dnode_of_tydef (tydef: _ Stmt.data_type): (_,_,_) decision_node =
  DN_match {
    dn_data_ty=tydef;
    dn_by_cstor=ID.Map.empty;
    dn_wildcard=[];
  }

let dnode_add_wildcard d x = match d with
  | DN_if (l,r) -> DN_if (x::l, x::r)
  | DN_match d -> DN_match { d with dn_wildcard=x :: d.dn_wildcard }
  | DN_bind d -> DN_bind (x::d)

let dnode_add_bool (d:(_,_,_) decision_node) b x = match d, b with
  | DN_if (l,r), `True -> DN_if (x::l,r)
  | DN_if (l,r), `False -> DN_if (l,x::r)
  | DN_bind _, _
  | DN_match _, _ ->
    errorf_ "@[<2>expected boolean decision node@]"

(* all constructors of [d] *)
let dnode_all_cstors (d:(_,_,_)decision_node_match) = Stmt.data_cstors d.dn_data_ty

(* add [x] to constructor [c] in node [d] *)
let dnode_add_cstor (d:(_,_,_)decision_node) c x = match d with
  | DN_match d ->
    let allowed_cstors = dnode_all_cstors d in
    if not (ID.Map.mem c allowed_cstors) then (
      errorf_ "@[<2>%a is not a constructor of %a@ (these are @[%a@])@]"
        ID.pp c ID.pp d.dn_data_ty.Stmt.ty_id
        (CCFormat.seq ID.pp) (ID.Map.keys allowed_cstors);
    );
    (* add [x] to the list [l] of subtrees already present for case [c] *)
    let l = try ID.Map.find c d.dn_by_cstor with Not_found -> [] in
    DN_match { d with dn_by_cstor = ID.Map.add c (x::l) d.dn_by_cstor }
  | DN_if _ -> errorf_ "cannot match against `@[%a@],@ boolean case" ID.pp c
  | DN_bind _ ->
    errorf_ "cannot match against `@[%a@]`,@ variable binding only" ID.pp c

(* A single equation with patterns in the left-hand side,
   being progressively converted to [id vars = rhs] along
   other equations to build a match tree. *)
type equation = {
  eqn_pats: pattern list; (* left-hand side patterns yet to convert *)
  eqn_rhs: term; (* eventual result of this branch *)
  eqn_side_conds: term list; (* side conditions *)
  eqn_subst: (ty,ty Var.t) Subst.t; (* current substitution *)
}

(* print function for debugging *)
let pp_eqn out (e:equation): unit =
  Format.fprintf out
    "{case @[<hv>[@[@[%a@]] -> `@[%a@]`@]@ when: [@[%a@]]@ with: @[%a@]@]}"
    (CCFormat.list pp_pat) e.eqn_pats
    P.pp e.eqn_rhs (CCFormat.list P.pp) e.eqn_side_conds
    (Subst.pp Var.pp_full) e.eqn_subst

let dnode_of_ty ~env (ty:ty): (_,_,ty) decision_node =
  if U.ty_is_Prop ty
  then DN_if ([], []) (* [v] is a prop, we use a if/then/else *)
  else begin match U.head_sym ty with
    | Some ty_id ->
      (* what does the type of [v] look like? *)
      begin match Env.def (Env.find_exn ~env ty_id) with
        | Env.Data (_, _, tydef) ->
          (* [v] is a variable of type (co)data, so we use the list
             of constructors to build a shallow pattern match *)
          dnode_of_tydef tydef
        | Env.Fun_def (_,_,_)
        | Env.Fun_spec _
        | Env.Pred _
        | Env.Copy_abstract _
        | Env.Copy_concrete _
        | Env.Cstor (_,_,_,_) ->
          errorf_ "@[`@[%a@]`@ is not a type.@]" ID.pp ty_id
        | Env.Copy_ty _
        | Env.NoDef ->
          (* [v] is of a non-matchable type, but we can still bind
             it to an (opaque) value *)
          DN_bind []
      end
    | None ->
      DN_bind [] (* not an atomic type *)
  end

(* We are matching [v] against equations' patterns,
   among which [List.hd e.eqn_pats], by accumulatin into [dnode]. *)
let dnode_add_eqn
    (v:ty Var.t)
    (dnode:(_,_,_)decision_node)
    (e:equation)
  : (_,_,_)decision_node =
  let pats = e.eqn_pats in
  let pat, pats_tail = match pats with [] -> assert false | x::y -> x,y in
  begin match pat with
    | P_any -> dnode_add_wildcard dnode {e with eqn_pats=pats_tail}
    | P_term t ->
      begin match Pat.repr t with
        | Pattern.Builtin ((`True | `False) as b) ->
          (* follow the [true] or [false] branch *)
          dnode_add_bool dnode b {e with eqn_pats=pats_tail}
        | Pattern.App (id,sub_pats) ->
          (* follow the [id] branch, with the new patterns *)
          let sub_pats = List.map (fun x->P_term x) sub_pats in
          dnode_add_cstor dnode id
            {e with eqn_pats = sub_pats @ pats_tail}
        | Pattern.Var v' ->
          (* renaming [v'] to [v] *)
          let subst =
            Subst.add ~subst:e.eqn_subst v' v
          in
          dnode_add_wildcard dnode {e with eqn_pats=pats_tail; eqn_subst=subst}
      end
  end

let add_path (lst:local_state) (v:ty Var.t) (p:pattern): local_state =
  let c = {path_var=v; path_pat=p} in
  { lst with path = c :: lst.path }

(* transform a list of left-nested equations into a match tree.

   @param vars list of distinct variables on the LHS of the new unique equation
   @param l the list of equations in the current branch
   invariant: [List.length vars = List.length e.eqn_pats] for every [e in l]
*)
let rec compile_equations lst vars (l:equation list) : term =
  begin match vars, l with
    | _, [] -> U.undefined_self lst.root (* undefined case *)
    | [], [{eqn_pats=[]; eqn_rhs; eqn_side_conds=[]; eqn_subst=subst}] ->
      (* simple case: no side conditions, one RHS *)
      Utils.debugf ~section 5
        "@[<2>compile by evaluating@ term: `@[%a@]`@ in: `@[%a@]`@]"
        (fun k->k P.pp eqn_rhs (Subst.pp Var.pp_full) subst);
      U.eval_renaming ~subst eqn_rhs
    | [], l ->
      (* reverse list, because the first clauses in pattern-match are the
         ones at the end of the list *)
      assert (List.for_all (fun e -> e.eqn_pats=[]) l);
      yield_list lst (List.rev l)
    | v::vars_tail, _ ->
      (* build one node of the decision tree *)
      let dnode =
        Utils.debugf ~section 5
          "@[<2>build decision node for `@[%a : %a@]`,@ @[tail: [@[%a@]]@]@ \
           with: @[<1>%a@]@ @[at: %a@]@]"
          (fun k->k Var.pp_full v P.pp (Var.ty v)
              (CCFormat.list Var.pp_full) vars_tail
              (CCFormat.list pp_eqn) l pp_path lst.path);
        let ty = Var.ty v in
        dnode_of_ty ~env:lst.env ty
      in
      let dnode =
        List.fold_left
          (fun dnode e -> dnode_add_eqn v dnode e)
          dnode l
      in
      compile_dnode lst v vars_tail dnode
  end

(* yield the term composed from the list [l] of cases. The first elements
   of [l] are prioritary w.r.t. the later ones. *)
and yield_list lst (l:equation list): term = match l with
  | [] -> assert false
  | [{eqn_side_conds=[]; _} as e] ->
    (* final case *)
    U.eval_renaming ~subst:e.eqn_subst e.eqn_rhs
  | [{eqn_side_conds=_::_; eqn_subst=subst; _} as e] ->
    (* final case, but might fail *)
    let else_ = U.undefined_self lst.root in
    let sides = List.map (U.eval_renaming ~subst) e.eqn_side_conds in
    U.ite (U.and_ sides) (U.eval_renaming ~subst e.eqn_rhs) else_
  | {eqn_rhs=t; eqn_side_conds=[]; eqn_subst=subst; _} :: _ :: _ ->
    Utils.warningf Utils.Warn_overlapping_match
      "@[ignore terms following `@[%a@]`, for it has no side condition@]" P.pp t;
    U.eval_renaming ~subst t
  | {eqn_side_conds=_::_; eqn_subst=subst; _} as e :: tail ->
    (* try [sides], yielding [t], otherwise fall back on [l'] *)
    let sides = List.map (U.eval_renaming ~subst) e.eqn_side_conds in
    U.ite (U.and_ sides)
      (U.eval_renaming ~subst e.eqn_rhs)
      (yield_list lst tail)

(* add missing constructors (not explicitely matched upon) to the set
   of cases, complemented with a list of fresh vars, leading to
   the default cases;
   then compile the subtrees *)
and compile_dnode lst v next_vars dn : term = match dn with
  | DN_if (l,r) ->
    let l = compile_equations (add_path lst v (P_term U.true_)) next_vars l in
    let r = compile_equations (add_path lst v (P_term U.false_)) next_vars r in
    U.ite (U.var v) l r
  | DN_bind l -> compile_equations lst next_vars l
  | DN_match dn when ID.Map.is_empty dn.dn_by_cstor ->
    (* no need to match, use next variables *)
    compile_equations (add_path lst v P_any) next_vars dn.dn_wildcard
  | DN_match dn ->
    (* one level of matching *)
    Utils.debugf ~section 5
      "@[<2>start compiling dnode,@ path: %a,@ wildcard: [@[%a@]]@] "
      (fun k->k pp_path lst.path (CCFormat.list pp_eqn) dn.dn_wildcard);
    (* the "default" case, if any *)
    let def =
      let map_missing =
        dnode_all_cstors dn
        |> ID.Map.filter (fun id _ -> not (ID.Map.mem id dn.dn_by_cstor))
        |> ID.Map.map (fun c -> List.length c.Stmt.cstor_args)
      in
      if ID.Map.is_empty map_missing
      then TI.Default_none (* exhaustive *)
      else (
        (* the default case is made of all equations that used "wildcard" *)
        let rhs =
          compile_equations (add_path lst v P_any) next_vars dn.dn_wildcard
        in
        TI.Default_some (rhs, map_missing)
      )
    (* per-constructor branches *)
    and l =
      dn.dn_by_cstor
      |> ID.Map.mapi
        (fun id cases ->
           Utils.debugf ~section 5
             "@[<2>compile_dnode for `%a` on cstor `%a`@ cases: [@[%a@]]@]"
             (fun k -> k Var.pp v ID.pp id (CCFormat.list pp_eqn) cases);
           (* fresh vars for the constructor's arguments *)
           let cstor = ID.Map.find id dn.dn_data_ty.Stmt.ty_cstors in
           let local_vars = List.mapi
               (fun i ty ->
                  Var.makef ~ty "%s_%d" (TyMo.mangle ~sep:"_" ty) (i+lst.offset))
               cstor.Stmt.cstor_args
           in
           (* the "wildcard" cases are relevant in all branches *)
           let wildcard_cases =
             List.map
               (fun e ->
                  let eqn_pats = List.map (fun _ -> P_any) local_vars @ e.eqn_pats in
                  {e with eqn_pats})
               dn.dn_wildcard
           in
           let lst = {lst with offset=lst.offset + List.length local_vars} in
           let lst =
             add_path lst v (P_term (U.app_const id (List.map U.var local_vars)))
           in
           let rhs' =
             compile_equations lst (local_vars @ next_vars) (cases @ wildcard_cases)
           in
           local_vars, rhs')
    in
    U.match_with (U.var v) l ~def

(* @param env the environment for types and constructors
   @param id the symbol being defined
*)
let uniq_eqns
  : env:env ->
  id:ID.t ->
  ty:T.t ->
  (term, term) Statement.equations ->
  (term, term) Statement.equations
  = fun ~env ~id ~ty e -> match e with
    | Stmt.Eqn_single _
    | Stmt.Eqn_app _ -> assert false
    | Stmt.Eqn_nested l ->
      (* create fresh vars *)
      let _, ty_args, _ = U.ty_unfold ty in
      let vars =
        List.mapi
          (fun i ty -> Var.makef ~ty "%s_%d" (TyMo.mangle ~sep:"_" ty) i)
          ty_args
      in
      let cases =
        List.map
          (fun (_,args,rhs,side) ->
             (* might need to add some (fresh) variables in [args] and [rhs] *)
             let eta_expand_args =
               vars
               |> CCList.drop (List.length args)
               |> List.map (fun v -> Var.fresh_copy v |> U.var)
             in
             let pats = List.map (fun t -> P_term t) (args @ eta_expand_args) in
             assert (List.length pats = List.length ty_args);
             { eqn_pats=pats;
               eqn_rhs=Red.app_whnf rhs eta_expand_args;
               eqn_side_conds=side;
               eqn_subst=Subst.empty;
             })
          l
      and lst = {
        root=U.app_const id (List.map U.var vars); (* defined term *)
        path=[]; offset=0; env;
      } in
      (* compile equations into flat pattern matches *)
      let new_rhs = compile_equations lst vars cases in
      Stmt.Eqn_single (vars,new_rhs)

let uniq_eqn_st env st =
  let loc = Stmt.loc st in
  let info = Stmt.info st in
  match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
      Utils.debugf ~section 5 "@[<2>compile equations@ `@[%a@]`@]"
        (fun k->k PStmt.pp_rec_defs l);
      let l' = List.map
          (fun def ->
             let d = Stmt.defined_of_rec def in
             let id = Stmt.id_of_defined d in
             let ty = Stmt.ty_of_defined d in
             let rec_eqns = uniq_eqns ~id ~ty ~env def.Stmt.rec_eqns in
             {def with Stmt.rec_eqns; })
          l
      in
      let env = Env.declare_rec_funs ?loc ~env l' in
      env, Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
      env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) ->
      env, Stmt.axiom ~info l
    | Stmt.Decl d ->
      let env = Env.declare_defined ?loc ~env d in
      env, Stmt.decl_of_defined ~info d
    | Stmt.TyDef (k,ty) ->
      (* declare (co)data, so it can be used in encoding *)
      let env = Env.def_data ?loc ~env ~kind:k ty in
      env, Stmt.mk_ty_def ~info k ty
    | Stmt.Pred (wf, k, l) ->
      let env = Env.def_preds ?loc ~env ~wf ~kind:k l in
      env, Stmt.mk_pred ~info ~wf k l
    | Stmt.Copy c ->
      let env = Env.add_copy ?loc ~env c in
      env, Stmt.copy ~info c
    | Stmt.Goal g ->
      env, Stmt.goal ~info g

let uniq_eqns_pb pb =
  let _, pb' =
    Problem.fold_map_statements pb
      ~f:uniq_eqn_st ~x:(Env.create())
  in
  pb'

let pipe ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after uniq equations@}: %a@]@." PPb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  and decode _ x = decode x in
  Transform.make
    ~on_encoded
    ~input_spec:Transform.Features.(of_list [Eqn, Eqn_nested])
    ~map_spec:Transform.Features.(update Eqn Eqn_single)
    ~name
    ~encode:(fun p ->
      let p = uniq_eqns_pb p in
      p, ()
    ) ~decode
    ()

