
(* This file is free software, part of nunchaku. See file "license" for more details. *)

open Nunchaku_core

module ID = ID
module Var = Var
module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)
module Subst = Var.Subst

module Card = Cardinality
module AT = AnalyzeType.Make(T)

type id = ID.t

let name = "elim_rec"

let section = Utils.Section.make name

exception Attr_is_handle_cstor

exception Attr_app_val

exception Attr_proto_val of ID.t * int

let fpf = Format.fprintf
let spf = CCFormat.sprintf

let () = Printexc.register_printer
  (function
    | Attr_app_val -> Some "app_symbol"
    | Attr_is_handle_cstor -> Some "handle_type"
    | Attr_proto_val (id, n) -> Some (spf "proto_%d_of_%a" n ID.print id)
    | _ -> None)

type term = T.t
type ty = T.t

(* how to encode a single recursive function/predicate *)
type fun_encoding = {
  fun_encoded_fun: id;
    (* name of function encoded this way *)
  fun_abstract_ty: ty;
    (* type of abstract values for the function *)
  fun_abstract_ty_id: id;
    (* symbol corresponding to [fun_abstract_ty] *)
  fun_concretization: (int * id * ty) list;
    (* for each parameter, concretization function, as an association list *)
  fun_ty: ty;
    (* original type *)
}

(* symbols used to eliminate higher-order funs *)
type hof_elim = {
  handle_ty : ID.t;
    (* the symbol used to reify type arrows into atomic types *)
  app_symbs : ID.Set.t;
    (* set of "app" symbols *)
}

type decode_state = {
  approx_fun : fun_encoding ID.Tbl.t;
    (* concretization_fun -> function it is used to encode *)
  encoded_fun : fun_encoding ID.Tbl.t;
    (* recursive function -> its encoding *)
  abstract_ty : fun_encoding ID.Tbl.t;
    (* set of abstraction types *)
  hof: hof_elim option;
    (* data related to higher-order functions, if any *)
}

(** {6 Encoding} *)

(* state used for the translation *)
type state = {
  decode: decode_state;
    (* for decoding purpose *)
  new_statements: (term, ty) Stmt.t CCVector.vector;
    (* additional statements to be added to the result, such as declarations *)
  env: (term,ty) Env.t;
    (* environment *)
  at_cache: AT.cache;
    (* for computing cardinalities of types *)
}

let create_state ~hof ~env () = {
  decode={
    approx_fun=ID.Tbl.create 16;
    encoded_fun=ID.Tbl.create 16;
    abstract_ty=ID.Tbl.create 16;
    hof;
  };
  new_statements=CCVector.create();
  env;
  at_cache=AT.create_cache ();
}

exception Error of string

exception TranslationFailed of term * string
(* not supposed to escape *)

exception DecodingFailed of T.t option * string

let fail_tr_ t msg =
  Utils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

let fail_decode_ ?term:t msg =
  Utils.exn_ksprintf msg ~f:(fun msg -> raise (DecodingFailed (t,msg)))

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

let () = Printexc.register_printer
  (function
    | TranslationFailed (t,msg) ->
        Some (spf "@[<2>translation of `@[%a@]` failed:@ %s@]" P.print t msg)
    | DecodingFailed (None, msg) ->
        Some (spf "@[<2>decoding failed:@ %s@]" msg)
    | DecodingFailed (Some t, msg) ->
        Some (spf "@[<2>decoding of `@[%a@]` failed:@ %s@]" P.print t msg)
    | Error msg -> Some (spf "@[<2>Error in ElimRec:@ %s@]" msg)
    | _ -> None)

let pp_hof out hof =
  fpf out "{@[handle_cstor=`%a`,@ app_syms=@[%a@]@]}"
    ID.print hof.handle_ty (ID.Set.print ID.print) hof.app_symbs

(* find the set of HOF-elim symbols used in [pb] *)
let gather_hof_ pb =
  let is_handle_ty attrs =
    List.exists
      (function
        | Stmt.Attr_exn Attr_is_handle_cstor -> true
        | _ -> false)
      attrs
  and is_app_ attrs =
    List.exists
      (function
        | Stmt.Attr_exn Attr_app_val -> true
        | _ -> false)
      attrs
  in
  let h_ty, app_m =
    Problem.statements pb
    |> CCVector.fold
      (fun ((h_ty, app_m) as acc) stmt -> match Stmt.view stmt with
        | Stmt.Decl (id, _, attrs) ->
            begin match is_handle_ty attrs, is_app_ attrs, h_ty with
            | true, _, None -> Some id, app_m (* found `to` *)
            | true, _, Some i2 ->
                errorf_ "both %a and %a are handle constructors, impossible"
                  ID.print id ID.print i2
            | false, true, _ -> h_ty, ID.Set.add id app_m
            | false, false, _ -> acc
            end
        | _ -> acc)
      (None, ID.Set.empty)
  in
  match h_ty with
  | None ->
      Utils.debug ~section 1
        "could not find the 'handle type constructor', assume absence of HOF";
      None
  | Some handle_ty -> Some { handle_ty; app_symbs=app_m; }

(* list of argument types that (monomorphic) type expects *)
let ty_args_ ty =
  let _, args, _ = U.ty_unfold ty in
  args

(* sort [fun_encoding.fun_concretization] *)
let sort_concretization = List.sort (fun (i,_,_)(j,_,_) -> CCInt.compare i j)

let pop_new_stmts_ ~state =
  let l = CCVector.to_list state.new_statements in
  CCVector.clear state.new_statements;
  l

(*
  - apply substitution eagerly (build it when we enter `forall_f x. f x = t`)
  - when we meet `f t1...tn`:
      - add 1 constraint `exists alpha. And_i (proj_i alpha = t_i)`;
      - keep same term
*)

let find_encoding ~state id : fun_encoding option =
  ID.Tbl.get state.decode.encoded_fun id

(* if [f] is a recursively defined function that is being eliminated,
    then return [Some def_of_f] *)
let as_defined_ ~state f = match T.repr f with
  | TI.Const id ->
      begin try
        Some (id, ID.Tbl.find state.decode.encoded_fun id)
      with Not_found -> None
      end
  | _ -> None

(* translate term/formula recursively into a new (guarded) term. *)
let rec tr_term_rec_ ~guards ~state subst t =
  match T.repr t with
  | TI.Const _ -> t
  | TI.Var v ->
      (* substitute if needed; no side-condition *)
      begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> t'
      end
  | TI.App (f,l) ->
      (* TODO: extend [as_defined_] so it also returns info about whether
         [f] is an 'app symbol'; in this case, later, we will add the
         'proto' case *)
      begin match as_defined_ ~state f with
        | Some (id, fundef) when guards ->
            (* [f] is a recursive function we are encoding *)
            if List.length l <> List.length fundef.fun_concretization
              then fail_tr_ t
                "defined function %a is partially applied (%d arguments, expected %d)"
                ID.print id (List.length l) (List.length fundef.fun_concretization);
            (* existential variable *)
            let alpha = Var.make ~name:"a" ~ty:fundef.fun_abstract_ty in
            let eqns = ref [] in
            let l' = List.map2
              (fun arg (_i, proj,_ty_proj) ->
                (* evaluate [arg] twice, the version without guards
                   will be used in the "asserting" *)
                let arg' = tr_term_rec_ ~guards ~state subst arg in
                let arg'_g = tr_term_rec_ ~guards:false ~state subst arg in
                let eqn = U.eq arg'_g (U.app (U.const proj) [U.var alpha]) in
                eqns := eqn :: !eqns;
                arg')
              l
              fundef.fun_concretization
            in
            let cond = U.exists alpha (U.and_ !eqns) in
            U.asserting (U.app f l') [cond]
        | Some _ ->
            (* do not introduce guards *)
            let f' = tr_term_rec_ ~guards:false ~state subst f in
            let l' = List.map (tr_term_rec_ ~guards:false ~state subst) l in
            U.app f' l'
        | None ->
            (* generic treatment *)
            tr_term_rec_' ~guards ~state subst t
      end
  | TI.Builtin (`True | `False | `DataSelect _ | `DataTest _) ->
        t (* partially applied, or constant *)
  | TI.Builtin ((`Undefined_self _ | `Undefined_atom _ | `Unparsable _) as b) ->
      U.builtin (TI.Builtin.map b ~f:(tr_term_rec_ ~guards ~state subst))
  | TI.Builtin (`Guard (t, g)) ->
      let t = tr_term_rec_ ~guards ~state subst t in
      let g' = TI.Builtin.map_guard (tr_term_rec_ ~guards ~state subst) g in
      U.guard t g'
  | TI.Bind (`Fun,_,_) -> fail_tr_ t "translation of λ impossible"
  | TI.Builtin (`Eq _ | `Ite _ | `And _ | `Or _ | `Not _ | `Imply _)
  | TI.Bind ((`Forall | `Exists | `Mu), _, _)
  | TI.Match _
  | TI.Let _ ->
      tr_term_rec_' ~guards ~state subst t
  | TI.TyBuiltin _
  | TI.TyArrow (_,_) -> t
  | TI.Bind (`TyForall, _, _)
  | TI.TyMeta _ -> assert false

and tr_term_rec_' ~guards ~state subst t =
  U.map subst t
    ~f:(tr_term_rec_ ~guards ~state)
    ~bind:U.rename_var

let tr_term ~state subst t =
  Utils.debugf ~section 4
    "@[<2>convert toplevel term@ `@[%a@]`@]" (fun k -> k P.print t);
  tr_term_rec_ ~guards:true ~state subst t

(* translate a top-level formula *)
let tr_form ~state t = tr_term ~state Subst.empty t

let as_var_exn_ t = match T.repr t with
  | TI.Var v -> v
  | _ -> fail_tr_ t "expected a variable"

(* add an [encoding] to the state *)
let add_encoding ~state fun_encoding =
  Utils.debugf ~section 5 "@[<2>add fun encoding for `%a`@]"
    (fun k->k ID.print fun_encoding.fun_encoded_fun);
  ID.Tbl.add state.decode.encoded_fun fun_encoding.fun_encoded_fun fun_encoding;
  ID.Tbl.add state.decode.abstract_ty fun_encoding.fun_abstract_ty_id fun_encoding;
  List.iter
    (fun (_,proj,_ty_proj) ->
      ID.Tbl.add state.decode.approx_fun proj fun_encoding)
    fun_encoding.fun_concretization;
  ()

(* create a new function encoding for the given (function) ID, and
   register it in state *)
let mk_fun_encoding_for_ ~state id =
  (* declare abstract type + projectors first *)
  let name = "G_" ^ ID.to_string_slug id in
  let abs_type_id = ID.make name in
  let abs_type = U.ty_const abs_type_id in
  let ty = Env.find_ty_exn ~env:state.env id in
  (* projection function: one per argument. It has
    type  [abs_type -> type of arg] *)
  let projectors =
    List.mapi
      (fun i ty_arg ->
        let id' = ID.make (Printf.sprintf "proj_%s_%d" name i) in
        let ty' = U.ty_arrow abs_type ty_arg in
        i, id', ty')
      (ty_args_ ty)
  in
  let fun_encoding = {
    fun_encoded_fun=id;
    fun_abstract_ty_id=abs_type_id;
    fun_abstract_ty=abs_type;
    fun_concretization=projectors;
    fun_ty=ty;
  } in
  add_encoding ~state fun_encoding;
  (* declare abstract type + projectors *)
  CCVector.push state.new_statements
    (Stmt.decl ~info:Stmt.info_default abs_type_id U.ty_type ~attrs:[]);
  List.iter
    (fun (_n,proj,ty_proj) ->
      CCVector.push state.new_statements
        (Stmt.decl ~info:Stmt.info_default proj ty_proj ~attrs:[]))
    fun_encoding.fun_concretization;
  fun_encoding

(* be sure that [id] has an encoding *)
let ensure_exists_encoding_ ~state id =
  if not (ID.Tbl.mem state.decode.encoded_fun id)
  then ignore (mk_fun_encoding_for_ ~state id)

let id_is_app_fun_ ~state id = match state.decode.hof with
  | None -> false
  | Some h -> ID.Set.mem id h.app_symbs

(* translate equation [eqn], which is defining the function
   corresponding to [fun_encoding] (if any).
   It returns an axiom instead. *)
let tr_eqns ~state ~(encoding:fun_encoding option) id eqn : term =
  let connect pol lhs rhs = match pol with
    | Polarity.Pos -> U.imply lhs rhs
    | Polarity.Neg -> U.imply rhs lhs
    | Polarity.NoPol -> U.eq lhs rhs
  in
  (* apply the projectors of fun_encoding to alpha
     @param first if true, keep first argument, else remove it *)
  let apply_projs ~keep_first fun_encoding alpha =
    fun_encoding.fun_concretization
    |> sort_concretization
    |> (fun l -> if keep_first then l else List.filter (fun (i,_,_) -> i<>0) l)
    |> List.map (fun (_,proj,_) -> U.app (U.const proj) [U.var alpha])
  in
  match eqn with
  | Stmt.Eqn_single (vars,rhs) ->
    begin match encoding with
    | Some fun_encoding ->
      assert (ID.equal id fun_encoding.fun_encoded_fun);
      (* quantify over abstract variable now *)
      let alpha = Var.make ~ty:fun_encoding.fun_abstract_ty ~name:"a" in
      (* replace each [x_i] by [proj_i var] *)
      assert (List.length vars = List.length fun_encoding.fun_concretization);
      let args' = apply_projs ~keep_first:true fun_encoding alpha in
      let subst = Subst.add_list ~subst:Subst.empty vars args' in
      (* convert right-hand side and add its side conditions *)
      let lhs = U.app_const fun_encoding.fun_encoded_fun args' in
      let rhs' = tr_term ~state subst rhs in
      (* how to connect [lhs] and [rhs]? *)
      let t = connect (ID.polarity id) lhs rhs' in
      if vars=[] then t else U.forall alpha t
    | None ->
      (* no abstract type *)
      let subst, vars' = Utils.fold_map U.rename_var Subst.empty vars in
      let lhs = U.app_const id (List.map U.var vars') in
      let rhs' = tr_term ~state subst rhs in
      (* how to connect [lhs] and [rhs]? *)
      let t = connect (ID.polarity id) lhs rhs' in
      U.forall_l vars' t
    end
  | Stmt.Eqn_app (_app_l, _vars, lhs, rhs) ->
      let root_id = id in
      (* traverse [lhs], making an encoding *)
      let rec traverse_lhs i subst t = match T.repr t with
        | TI.Const _ -> t, subst, []
        | TI.App (f, l) ->
            begin match T.repr f, l with
            | _, [] -> assert false
            | TI.Const f_id, first_arg :: l' ->
              begin match find_encoding ~state f_id with
              | Some fun_encoding ->
                (* variable of the abstract type of [f_id] *)
                let alpha = Var.makef "a_%d" i ~ty:fun_encoding.fun_abstract_ty in
                if id_is_app_fun_ ~state f_id then (
                  (* first case: application symbol. We need to recurse
                     in the first argument *)
                  let first_arg', subst, vars = traverse_lhs (i+1) subst first_arg in
                  let l'_as_vars = List.map as_var_exn_ l' in
                  let new_l' = apply_projs ~keep_first:false fun_encoding alpha in
                  let subst = Var.Subst.add_list ~subst l'_as_vars new_l' in
                  let t' = U.app f (first_arg' :: new_l') in
                  t', subst, alpha :: vars
                ) else (
                  (* regular function, should have only variables as
                     arguments *)
                  assert (ID.equal f_id root_id);
                  let l_as_vars = List.map as_var_exn_ l in
                  let new_args = apply_projs ~keep_first:true fun_encoding alpha in
                  let subst = Subst.add_list ~subst l_as_vars new_args in
                  let t' = U.app f new_args in
                  t', subst, [alpha]
                )
              | None ->
                if id_is_app_fun_ ~state f_id then (
                  (* first case: application symbol. We need to recurse
                     in the first argument *)
                  let first_arg', subst, vars = traverse_lhs (i+1) subst first_arg in
                  let l'_as_vars = List.map as_var_exn_ l' in
                  let t' = U.app f (first_arg' :: List.map U.var l'_as_vars) in
                  t', subst, l'_as_vars @ vars
                ) else (
                  (* regular function, should have only variables as
                     arguments *)
                  assert (ID.equal f_id root_id);
                  let l_as_vars = List.map as_var_exn_ l in
                  let t' = U.app f (List.map U.var l_as_vars) in
                  t', subst, l_as_vars
                )
              end
            | _ -> assert false (* incorrect shape *)
            end
        | _ -> assert false
      in
      let lhs', subst, vars' = traverse_lhs 0 Subst.empty lhs in
      let rhs' = tr_term ~state subst rhs in
      let form = connect Polarity.NoPol lhs' rhs' in
      U.forall_l vars' form
  | Stmt.Eqn_nested _ -> assert false

(* transform the recursive definition (mostly, its equations) *)
let tr_rec_def ~state ~encoding def =
  let id = Stmt.defined_of_rec def |> Stmt.id_of_defined in
  tr_eqns ~state ~encoding id def.Stmt.rec_eqns

let card_ty_ ~state (ty:ty) : Card.t =
  AT.cardinality_ty ~cache:state.at_cache state.env ty

(* cardinality of this tuple *)
let card_tys_ ~state l : Card.t = match l with
  | [] -> Card.one
  | _ -> Card.product (List.map (card_ty_ ~state) l)

(* given [id : ty] a recursive function, should we encode its domain?
   This is a heuristic if [ty = a1 -> a2 -> ... -> ak -> ret] where
    each [a_i] is finite; otherwise we MUST box. *)
let should_box_ ~state id ty : bool =
  let module Z = Card.Z in
  let _, args, _ = U.ty_unfold ty in
  assert (args <> []);
  let card = card_tys_ ~state args in
  let res = match card with
    | Card.Unknown
    | Card.Infinite -> true
    | Card.Exact c
    | Card.QuasiFiniteGEQ c ->
      (* should box if [z >= 30] *)
      Z.compare c (Z.of_int 30) >= 0
  in
  Utils.debugf ~section 2
    "@[<2>@{<Cyan>decision to box@} `@[%a : %a@]`:@ %B (card of domain = %a)@]"
    (fun k->k ID.print id P.print ty res Card.print card);
  res

(* transform each axiom, considering case_head as rec. defined. *)
let tr_rec_defs ~info ~state l =
  (* first, build and register an encoding for each defined function *)
  let ty_decls = CCList.flat_map
    (fun def ->
      let d = Stmt.defined_of_rec def in
      let id = Stmt.id_of_defined d in
      let ty = Stmt.ty_of_defined d in
      (* declare the function, since it is not longer "rec defined",
         but only axiomatized *)
      let st = Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty in
      (* decide whether to box the function's arguments *)
      if should_box_ ~state id ty
      then (
        (* compute encoding afterwards (order matters! because symbols
           needed for the encoding also depend on [id] being declared) *)
        let _ = mk_fun_encoding_for_ ~state id in
        let st_l = pop_new_stmts_ ~state in
        st :: st_l
      ) else
        (* just the declaration, since we do not box *)
        [st])
    l
  in
  (* then translate each definition *)
  let l' = List.map
    (fun def ->
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      let encoding = find_encoding ~state id in
      try
        tr_rec_def ~state ~encoding def
      with TranslationFailed (t, msg) as e ->
        (* could not translate, keep old definition *)
        Utils.debugf ~section 1
          "@[<2>recursion elimination in@ @[%a@]@ \
            failed on subterm @[%a@]:@ %s@]"
            (fun k -> k PStmt.print (Stmt.axiom_rec ~info l) P.print t msg);
        raise e)
    l
  in
  ty_decls @ [Stmt.axiom ~info l']

(* translate a statement *)
let tr_statement ~state st =
  let info = Stmt.info st in
  let stmts' = match Stmt.view st with
  | Stmt.Decl (id,l,attrs) ->
      (* app symbol: needs encoding *)
      if id_is_app_fun_ ~state id then ensure_exists_encoding_ ~state id;
      (* in any case, no type declaration changes *)
      Stmt.decl ~info ~attrs id l :: pop_new_stmts_ ~state
  | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l] (* no (co) data changes *)
  | Stmt.Pred _ -> assert false (* typing: should be absent *)
  | Stmt.Axiom l ->
      begin match l with
      | Stmt.Axiom_rec l ->
          tr_rec_defs ~info ~state l
      | Stmt.Axiom_spec spec ->
          let spec' =
            Stmt.map_spec_defs ~term:(tr_form ~state) ~ty:CCFun.id spec
          in
          [Stmt.axiom_spec ~info spec']
      | Stmt.Axiom_std l ->
          let l = List.map
            (fun t -> tr_form ~state t)
            l in
          [Stmt.axiom ~info l]
      end
  | Stmt.Copy c -> [Stmt.copy ~info c]
  | Stmt.Goal g ->
      [Stmt.goal ~info (tr_form ~state g)]
  in
  (* add the new statements before *)
  let stmts'' = pop_new_stmts_ ~state in
  stmts'' @ stmts'

let elim_recursion pb =
  let hof = gather_hof_ pb in
  let env = Problem.env pb in
  Utils.debugf ~section 3 "@[<2>hof info:@ @[%a@]@]"
    (fun k->k (CCFormat.opt pp_hof) hof);
  let state = create_state ~hof ~env () in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(tr_statement ~state)
  in
  pb', state.decode

(** {6 Decoding}

  We expect to get back a model where the encoded functions (and their
  projections) are decision trees over finite domains.

  To make things more readable for the user, we drop the projections
  from the model, and limit the encoded functions to the
  domain where their projections were defined (the domain on which it
  is not garbage) *)

type finite_domain = {
  dom_fun: fun_encoding;
    (* function *)
  dom_dom: ID.t list;
    (* abstract domain *)
  mutable dom_args: term list ID.Map.t;
    (* for each abstract value in the approximation type, the list of
       concrete arguments it corresponds to *)
}

type finite_domains = finite_domain ID.Tbl.t
(* map abstracted function -> its domain *)

let pp_domain out d =
  let pp_tuple out (id,l) =
    fpf out "%a → (@[%a@])" ID.print id
      (CCFormat.list ~start:"" ~stop:"" P.print) l
  in
  fpf out "[@[<v2>`%a`:@ %a@]]"
    ID.print d.dom_fun.fun_encoded_fun
    (CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_tuple) (ID.Map.to_seq d.dom_args)

type proj_fun = {
  proj_var: T.t Var.t;
    (* argument to the projection function *)

  proj_tree: (T.t, T.t) Model.decision_tree;
    (* decision tree for the variable *)
}

module DT_util = Model.DT_util(T)

(*
   - gather definitions of projections
   - gather domains of abstract types
*)
let pass1_ ~state m =
  let projs : proj_fun ID.Tbl.t = ID.Tbl.create 16 in
  let doms  : finite_domain ID.Tbl.t = ID.Tbl.create 16 in
  Model.iter m
    ~constants:(fun (t,_,_) -> match T.repr t with
      | TI.Const id ->
          (* a function should not be modeled by a constant *)
          assert (not (ID.Tbl.mem state.approx_fun id));
      | _ -> ())
    ~funs:(fun (t,vars,body,_) -> match T.repr t, vars with
      | TI.Const id, [v] ->
          (* register the model for this approximated function *)
          if ID.Tbl.mem state.approx_fun id
          then ID.Tbl.add projs id {proj_var=v; proj_tree=body; }
      | _, _ -> ())
    ~finite_types:(fun (ty,dom) -> match T.repr ty with
      | TI.Const id ->
          begin try
            let dom_fun = ID.Tbl.find state.abstract_ty id in
            let dom = {dom_fun; dom_dom=dom; dom_args=ID.Map.empty; } in
            ID.Tbl.add doms dom_fun.fun_encoded_fun dom
          with Not_found -> ()
          end
      | _ -> ());
    projs, doms

(* compute map `abstract type -> set of tuples by projection`.
 Update doms. *)
let pass2_ projs (doms:finite_domains) =
  ID.Tbl.iter
    (fun _ fdom ->
      List.iter
        (fun val_id ->
          let args =
            fdom.dom_fun.fun_concretization
            |> sort_concretization
            |> List.map
              (fun (_,f_id,_) ->
                let proj =
                  try ID.Tbl.find projs f_id
                  with Not_found ->
                    fail_decode_ "could not find value of projection function %a on %a"
                      ID.print f_id ID.print val_id
                in
                let subst = Var.Subst.singleton proj.proj_var (U.const val_id) in
                DT_util.eval ~subst proj.proj_tree)
          in
          fdom.dom_args <- ID.Map.add val_id args fdom.dom_args)
        fdom.dom_dom)
    doms;
  ()

(* translate definitions of rec. functions based on
    the map (only keep in the domain, tuples that are obtained by
    projections, the rest is junk)
*)
let pass3_ ~state doms m =
  (* decode a function. *)
  let decode_fun_ dom vars body =
    let arity = List.length dom.dom_fun.fun_concretization in
    if List.length vars <> arity
      then fail_decode_
        ~term:(U.fun_l vars (DT_util.to_term body))
        "expected a function of %d arguments" arity;
    (* compute value of the function applied to [tup] *)
    let apply_to tup =
      let subst = Subst.add_list ~subst:Subst.empty vars tup in
      DT_util.eval ~subst body
    in
    (* set of tuples on which the function is defined *)
    let dom_tuples = ID.Map.to_list dom.dom_args |> List.map snd in
      (* default case: undefined
        TODO: if initial domain was finite, this might be unecessary,
          because CVC4 could model the whole domain? *)
    let default =
      U.app (U.undefined_atom ~ty:dom.dom_fun.fun_ty) (List.map U.var vars)
    in
    let new_body =
      List.map
        (fun tup ->
          let test = List.combine vars tup in
          let then_ = apply_to tup in
          test, then_)
        dom_tuples
    in
    Model.DT.test new_body ~else_:default
  in
  (* now remove projections and filter recursion functions's values *)
  Model.filter_map m
    ~constants:(fun (t,u,k) -> match T.repr t with
      | TI.Const id when ID.Tbl.mem state.approx_fun id ->
          None (* drop approximation functions *)
      | _ -> Some (t,u,k))
    ~funs:(fun (t,vars,body,k) -> match T.repr t with
      | TI.Const id when ID.Tbl.mem state.approx_fun id ->
          None (* drop approximation functions *)
      | TI.Const f_id when ID.Tbl.mem state.encoded_fun f_id ->
          (* remove junk from the definition of [t] *)
          let body' = decode_fun_ (ID.Tbl.find doms f_id) vars body in
          Utils.debugf ~section 3
            "@[<hv2>decoding of recursive fun @[%a %a@] :=@ `@[%a@]`@ is `@[%a@]`@]"
            (fun k->k ID.print f_id (CCFormat.list Var.print_full) vars
            (Model.DT.print P.print') body (Model.DT.print P.print') body');
          Some (t, vars, body',k)
      | _ ->
          (* keep *)
          Some (t,vars,body,k))
    ~finite_types:(fun ((ty,_) as pair) -> match T.repr ty with
      | TI.Const id when ID.Tbl.mem state.abstract_ty id ->
          None (* remove abstraction types *)
      | _ -> Some pair)

let decode_model ~state m =
  Utils.debugf ~section 3 "@[<2>decode model:@ @[%a@]@]"
    (fun k->k (Model.print P.print' P.print) m);
  let projs, domains = pass1_ ~state m in
  pass2_ projs domains;
  Utils.debugf ~section 2 "@[<2>domains:@ @[%a@]@]"
    (fun k->k (CCFormat.seq ~start:"" ~stop:"" pp_domain) (ID.Tbl.values domains));
  let m = pass3_ ~state domains m in
  Utils.debugf ~section 3 "@[<2>model after decoding:@ @[%a@]@]"
    (fun k->k (Model.print P.print' P.print) m);
  m

(** {6 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after elimination of recursion@}: %a@]@." PPb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  Transform.make
    ~on_encoded ?on_decoded
    ~input_spec:Transform.Features.(of_list [Ty, Mono; Eqn, Eqn_app; Ind_preds, Absent])
    ~map_spec:Transform.Features.(update Eqn Absent)
    ~name
    ~encode:(fun p ->
      let p, state = elim_recursion p in
      p, state
    )
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after elim_rec@}:@ %a@]@."
         (Problem.Res.print P.print' P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model ~state) in
  pipe_with ~on_decoded ~print ~decode ~check
