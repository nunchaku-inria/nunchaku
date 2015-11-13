
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Var = NunVar
module TI = NunTermInner
module TyI = NunTypeMono
module Stmt = NunStatement
module Sig = NunSignature

type id = ID.t

let section = NunUtils.Section.make "recursion_elim"

type inv1 = <ty:[`Mono]; eqn:[`Linear]>
type inv2 = <ty:[`Mono]; eqn:[`Nested]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)
  module Subst = Var.Subst
  module TyM = NunTypeMono.Make(T)

  type term = T.t

  (* how to encode a single recursive function/predicate *)
  type fun_encoding = {
    fun_abstract_ty: term;
      (* type of abstract values for the function *)
    fun_concretization: (id * term) list;
      (* for each parameter, concretization function *)
  }

  type decode_state = {
    approx_fun : fun_encoding ID.Tbl.t;
      (* concretization_fun -> function it is used to encode *)
  }

  (* state used for the translation *)
  type state = {
    decode: decode_state;
      (* for decoding purpose *)
    fun_encodings: fun_encoding ID.Tbl.t;
      (* function -> encoding for that function *)
    mutable sigma: term Sig.t;
      (* signature *)
  }

  let create_state() = {
    decode={approx_fun=ID.Tbl.create 16;};
    fun_encodings=ID.Tbl.create 16;
    sigma=Sig.empty;
  }

  exception TranslationFailed of term * string
  (* not supposed to escape *)

  let fail_tr_ t msg =
    NunUtils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

  type polarity =
    | Pos
    | Neg
    | NoPolarity

  type local_state = {
    pol: polarity;
      (* local polarity *)
    subst: (term,term) Subst.t;
      (* local substitution *)
  }

  let empty_local_state = {pol=Pos; subst=Subst.empty; }

  let inv_pol ls = {ls with
    pol=(match ls.pol with | Pos -> Neg | Neg -> Pos | NoPolarity -> NoPolarity)
  }

  let no_pol ls = {ls with pol=NoPolarity}

  (* is this symbol a predicate? *)
  let is_bool_ ~state id =
    let ty = Sig.find_exn ~sigma:state.sigma id in
    let ty_ret = U.ty_returns ty in
    match TyM.repr ty_ret with
    | TyI.Builtin `Prop -> true
    | TyI.Builtin `Kind
    | TyI.Builtin `Type -> false
    | TyI.Const _ | TyI.App _ | TyI.Arrow _ -> false

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match TyM.repr ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

  (* is [t] a variable bound in [local_state.subst]? *)
  let is_var_in_subst_ ~local_state t = match T.repr t with
    | TI.Var v when Subst.mem ~subst:local_state.subst v -> true
    | _ -> false

  let mk_and_ = function
    | [] -> U.app_builtin `True []
    | [x] -> x
    | l -> U.app_builtin `And l

  let mk_not_ t = U.app_builtin `Not [t]

  let mk_or_ = function
    | [] -> U.app_builtin `False []
    | [x] -> x
    | l -> U.app_builtin `Or l

  let mk_imply_ a b = U.app_builtin `Imply [a; b]

  (* combine side-conditions with [t], depending on polarity *)
  let add_conds pol t conds = match pol with
    | Pos -> mk_and_ [t; mk_and_ conds], []
    | Neg -> mk_or_ [t; mk_not_ (mk_and_ conds)], []
    | NoPolarity -> t, conds

  (* TODO:
    - apply substitution eagerly (build it when we enter `forall_f x. f x = t`)
    - when we meet `f t1...tn`:
        - add 1 constraint `exists alpha. And_i (proj_i alpha = t_i)`;
        - keep same term
  *)

  (* if [f] is a recursively defined function that is being eliminated,
      then return [Some def_of_f] *)
  let as_defined_ ~state f = match T.repr f with
    | TI.Const id ->
        begin try
          Some (id, ID.Tbl.find state.fun_encodings id)
        with Not_found -> None
        end
    | _ -> None

  (* translate term/formula recursively. Returns new term and a list
    of side-conditions (guards) *)
  let rec tr_term_rec_ ~state ~local_state (t:term): term * term list =
    match T.repr t with
    | TI.Const _ -> t, []
    | TI.Var v ->
        (* substitute if needed; no side-condition *)
        let t' = match Subst.find ~subst:local_state.subst v with
          | None -> t
          | Some t' -> t'
        in t', []
    | TI.App (f,l) ->
        begin match as_defined_ ~state f with
          | Some (id, fundef) ->
              (* [f] is a recursive function we are encoding *)
              if List.length l <> List.length fundef.fun_concretization
                then fail_tr_ t
                  "defined function %a is partially applied (%d arguments, expected %d)"
                  ID.print_name id (List.length l) (List.length fundef.fun_concretization);
              (* existential variable *)
              let alpha = Var.make ~name:"a" ~ty:fundef.fun_abstract_ty in
              let conds = ref [] in
              let eqns = ref [] in
              let l' = List.map2
                (fun arg (proj,_ty_proj) ->
                  let arg', cond_arg = tr_term_rec_ ~state ~local_state arg in
                  let eqn = U.eq arg' (U.app (U.const proj) [U.var alpha]) in
                  eqns := eqn :: !eqns;
                  conds := cond_arg @ !conds;
                  arg'
                )
                l
                fundef.fun_concretization
              in
              conds := (U.exists alpha (mk_and_ !eqns)) :: !conds;
              U.app f l', !conds
          | None ->
              (* combine side conditions from every sub-term *)
              let conds, l' = NunUtils.fold_map
                (fun conds t ->
                  let t', c = tr_term_rec_ ~state ~local_state t in
                  List.rev_append c conds, t'
                )
                [] l
              in
              U.app f l', conds
        end
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | `True ,_
        | `False ,_ -> t, []
        | `Not, [t] ->
            let t, cond = tr_term_rec_ ~state ~local_state:(inv_pol local_state) t in
            add_conds local_state.pol (mk_not_ t) cond
        | `Or, l
        | `And, l ->
            let l_conds = List.map (tr_term_rec_ ~state ~local_state) l in
            let l, conds = List.split l_conds in
            add_conds local_state.pol (U.app_builtin b l) (List.flatten conds)
        | `Imply, [a;b] ->
            let a, cond_a = tr_term_rec_ ~state ~local_state:(inv_pol local_state) a in
            let b, cond_b = tr_term_rec_ ~state ~local_state b in
            add_conds local_state.pol (U.app b [a; b]) (List.append cond_a cond_b)
        | `Equiv, _ -> fail_tr_ t "cannot translate equivalence (polarity)"
        | `Ite, [a;b;c] ->
            let a, cond_a = tr_term_rec_ ~state ~local_state:(no_pol local_state) a in
            let b, cond_b = tr_term_rec_ ~state ~local_state b in
            let c, cond_c = tr_term_rec_ ~state ~local_state c in
            add_conds local_state.pol
              (U.app_builtin `Ite [a;b;c])
              (List.flatten [cond_a; cond_b; cond_c])
        | `Eq, [a;b] ->
            let a, cond_a = tr_term_rec_ ~state ~local_state a in
            let b, cond_b = tr_term_rec_ ~state ~local_state b in
            add_conds local_state.pol
              (U.app_builtin `Eq [a;b])
              (List.append cond_a cond_b)
        | `DataTest _, [t]
        | `DataSelect (_,_), [t] ->
            let t', conds = tr_term_rec_ ~state ~local_state t in
            U.app_builtin b [t'], conds
        | `Not,_ | `Imply,_ | `Ite,_
        | `Eq,_ | `DataSelect _,_ | `DataTest _,_ ->
            assert false (* wrong arity *)
        end
    | TI.Bind (`Forall,v,t) ->
        let t', conds = tr_term_rec_ ~state ~local_state t in
        U.forall v t', List.map (U.forall v) conds
    | TI.Bind (`Exists,v,t) ->
        let t, cond = tr_term_rec_ ~state ~local_state t in
        add_conds local_state.pol (U.exists v t) cond
    | TI.Bind (`Fun,_,_) -> fail_tr_ t "translation of λ impossible"
    | TI.Let (v,t,u) ->
        let t, c1 = tr_term_rec_ ~state ~local_state t in
        let u, c2 = tr_term_rec_ ~state ~local_state u in
        U.let_ v t u, List.append c1 c2
    | TI.Match (t, l) ->
        let t, ct = tr_term_rec_ ~state ~local_state t in
        let conds' = ref [] in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let rhs, conds = tr_term_rec_ ~state ~local_state rhs in
            conds' := conds @ !conds';
            vars,rhs
          ) l
        in
        U.match_with t l, ct @ !conds'
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, []
    | TI.Bind (`TyForall, _, _)
    | TI.TyMeta _ -> assert false

  let tr_term ~state ~local_state t =
    NunUtils.debugf ~section 4
      "@[<2>convert toplevel term `@[%a@]`@]" (fun k -> k P.print t);
    tr_term_rec_ ~state ~local_state t

  (* translate a top-level formula
   TODO: shall we actually keep the conditions? *)
  let tr_form ~state t =
    let t', conds = tr_term ~state ~local_state:empty_local_state t in
    mk_imply_ (mk_and_ conds) t'

  (* translate equation [eqn], which is defining the function
     corresponding to [fun_encoding] *)
  let tr_eqn ~state ~fun_encoding eqn =
    let Stmt.Eqn_linear (vars,rhs,side) = eqn in
    (* quantify over abstract variable now *)
    let alpha = Var.make ~ty:fun_encoding.fun_abstract_ty ~name:"a" in
    (* replace each [x_i] by [proj_i var] *)
    assert (List.length vars = List.length fun_encoding.fun_concretization);
    let args' = List.map
      (fun (proj,_) -> U.app (U.const proj) [U.var alpha])
      fun_encoding.fun_concretization
    in
    let subst = Subst.add_list ~subst:Subst.empty vars args' in
    let local_state = { empty_local_state with subst; } in
    (* convert right-hand side (ignore its side conditions) *)
    let rhs', conds = tr_term ~state ~local_state rhs in
    (* need to invert polarity, side conditions are LHS of => *)
    let conds_side, side' = NunUtils.fold_map
      (fun conds t ->
        let t', conds' = tr_term ~state ~local_state:(inv_pol local_state) t in
        List.rev_append conds' conds, t'
      ) conds side
    in
    Stmt.Eqn_nested ([alpha], args', rhs', conds_side @ side')

  (* transform the recursive definition (mostly, its equations) *)
  let tr_rec_def ~state ~fun_encoding def =
    let eqns' = List.map
      (tr_eqn ~state ~fun_encoding)
      def.Stmt.rec_eqns
    in
    (* return new set of equations *)
    {def with Stmt.rec_eqns=eqns'}

  let tr_rec_defs ~info ~state l =
    (* transform each axiom, considering case_head as rec. defined *)
    let new_stmts = ref [] in
    let add_stmt = CCList.Ref.push new_stmts in
    (* first, build and register an encoding for each defined function *)
    List.iter
      (fun def ->
        let id = def.Stmt.rec_defined.Stmt.defined_head in
        (* declare abstract type + projectors first *)
        let name = "G_" ^ ID.name id in
        let abs_type_id = ID.make ~name in
        let abs_type = U.ty_const abs_type_id in
        let ty = Sig.find_exn ~sigma:state.sigma id in
        (* projection function: one per argument. It has
          type  [abs_type -> type of arg] *)
        let projectors =
          List.mapi
            (fun i ty_arg ->
              let id' = ID.make ~name:(Printf.sprintf "proj_%s_%d" name i) in
              id', U.ty_arrow abs_type ty_arg
            )
            (ty_args_ ty)
        in
        let fun_encoding = {
          fun_abstract_ty=abs_type;
          fun_concretization=projectors;
        } in
        ID.Tbl.add state.fun_encodings id fun_encoding;
        (* declare abstract type + projectors *)
        add_stmt (Stmt.ty_decl ~info:Stmt.info_default abs_type_id U.ty_type);
        List.iter
          (fun (proj,ty_proj) ->
            add_stmt (Stmt.decl ~info:Stmt.info_default proj ty_proj);
          )
          fun_encoding.fun_concretization;
      )
      l;
    (* then translate each definition *)
    let l' = List.map
      (fun def ->
        try
          let id = def.Stmt.rec_defined.Stmt.defined_head in
          let fun_encoding = ID.Tbl.find state.fun_encodings id in
          tr_rec_def ~state ~fun_encoding def
        with TranslationFailed (t, msg) as e ->
          (* could not translate, keep old definition *)
          NunUtils.debugf ~section 1
            "[<2>recursion elimination in@ @[%a@]@ \
              failed on subterm @[%a@]:@ %s@]"
              (fun k -> k PStmt.print (Stmt.axiom_rec ~info l) P.print t msg);
          raise e
      )
      l
    in
    (* add new statements (type declarations) before l' *)
    List.rev_append !new_stmts [Stmt.axiom_rec ~info l']

  (* translate a statement *)
  let tr_statement ~state st =
    (* update signature *)
    state.sigma <- Sig.add_statement ~sigma:state.sigma st;
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Decl (id,k,l) -> [Stmt.mk_decl ~info id k l] (* no type declaration changes *)
    | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l] (* no (co) data changes *)
    | Stmt.Axiom l ->
        begin match l with
        | Stmt.Axiom_rec l ->
            tr_rec_defs ~info ~state l
        | Stmt.Axiom_spec spec ->
            let axioms' =
              List.map
                (fun t -> tr_form ~state t)
                spec.Stmt.spec_axioms
            in
            [Stmt.axiom_spec ~info {spec with Stmt.spec_axioms=axioms'}]
        | Stmt.Axiom_std l ->
            let l = List.map
              (fun t -> tr_form ~state t)
              l in
            [Stmt.axiom ~info l]
        end
    | Stmt.Goal g ->
        [Stmt.goal ~info (tr_form ~state g)]

  let elim_recursion pb =
    let state = create_state() in
    let pb' = NunProblem.flat_map_statements ~f:(tr_statement ~state) pb in
    pb', state.decode

  let decode_term ~state:_ (t:term) = t (* TODO *)

  let decode_model ~state m =
    NunModel.map ~f:(decode_term ~state) m

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = NunProblem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of recursion: %a@]@." PPb.print]
      else []
    in
    NunTransform.make1
      ~on_encoded
      ~name:"recursion_elim"
      ~encode:(fun p ->
        let p, state = elim_recursion p in
        p, state
      )
      ~decode:(fun state x ->
        let decode_term = decode_term ~state in
        decode ~decode_term x
      )
      ()

  let pipe ~print =
    let decode ~decode_term = NunModel.map ~f:decode_term in
    pipe_with ~print ~decode
end
