
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Var = NunVar
module TyI = NunType_intf
module TI = NunTerm_intf
module Stmt = NunStatement
module Sig = NunSignature

type id = ID.t

let section = NunUtils.Section.make "recursion_elim"

module Make(T : NunTerm_ho.S) = struct
  module PrintT = NunTerm_ho.Print(T)

  (* how to encode a single recursive function/predicate *)
  type fun_encoding = {
    fun_abstract_ty: T.ty;
      (* type of abstract values for the function *)
    fun_concretization: (ID.t * T.ty) list;
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
    mutable sigma: T.ty Sig.t;
      (* signature *)
  }

  let create_state() = {
    decode={approx_fun=ID.Tbl.create 16;};
    fun_encodings=ID.Tbl.create 16;
    sigma=Sig.empty;
  }

  exception TranslationFailed of T.t * string
  (* not supposed to escape *)

  let fail_tr_ t msg = raise (TranslationFailed (t,msg))

  type polarity =
    | Pos
    | Neg
    | NoPolarity

  type local_state = {
    defining: (T.ty Var.t * fun_encoding) option;
      (* the function we are defining recursively (if any), and its
          abstract type and projectors *)
    pol: polarity;
      (* local polarity *)
  }

  let inv_pol ls = {ls with
    pol=(match ls.pol with | Pos -> Neg | Neg -> Pos | NoPolarity -> NoPolarity)
  }

  let no_pol ls = {ls with pol=NoPolarity}

  (* is this symbol a predicate? *)
  let is_bool_ ~state id =
    let ty = Sig.find_exn ~sigma:state.sigma id in
    let ty_ret = T.Ty.returns ty in
    let module B = NunBuiltin.Ty in
    match T.Ty.view ty_ret with
    | TyI.Builtin B.Prop -> true
    | TyI.Builtin B.Kind
    | TyI.Builtin B.Type -> false
    | TyI.Const _
    | TyI.Var _
    | TyI.Meta _
    | TyI.App (_,_)
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> false

  module B = NunBuiltin.T

  let mk_and_ = function
    | [] -> T.app_builtin B.True []
    | [x] -> x
    | l -> T.app_builtin B.And l

  let mk_not_ t = T.app_builtin B.Not [t]

  let mk_or_ = function
    | [] -> T.app_builtin B.False []
    | [x] -> x
    | l -> T.app_builtin B.Or l

  (* combine side-conditions with [t], depending on polarity *)
  let add_conds pol t conds = match pol with
    | Pos -> mk_and_ [t; mk_and_ conds], []
    | Neg -> mk_or_ [t; mk_not_ (mk_and_ conds)], []
    | NoPolarity -> t, conds

  (* translate term/formula recursively. Returns new term and a list
    of side-conditions (guards) *)
  let rec tr_term ~state ~local_state t =
    match T.view t with
    | TI.TyMeta _ -> assert false
    | TI.Const _ -> t, []
    | TI.Var _ -> t, []
    | TI.App (f,l) ->
        begin match T.view f, local_state.defining with
          | TI.Var v, Some (v', fundef) when Var.equal v v'  ->
              (* we are defining this particular function *)
              assert false (* TODO *)
          | TI.Const _, _ -> assert false
          | _ -> assert false (* TODO *)
        end
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | B.True ,_
        | B.False ,_ -> t, []
        | B.Not, [t] ->
            let t, cond = tr_term ~state ~local_state:(inv_pol local_state) t in
            add_conds local_state.pol (mk_not_ t) cond
        | B.Or, l
        | B.And, l ->
            let l_conds = List.map (tr_term ~state ~local_state) l in
            let l, conds = List.split l_conds in
            add_conds local_state.pol (T.app_builtin b l) (List.flatten conds)
        | B.Imply, [a;b] ->
            let a, cond_a = tr_term ~state ~local_state:(inv_pol local_state) a in
            let b, cond_b = tr_term ~state ~local_state b in
            add_conds local_state.pol (T.app b [a; b]) (List.append cond_a cond_b)
        | B.Equiv, _ -> fail_tr_ t "cannot translate equivalence (polarity)"
        | B.Ite, [a;b;c] ->
            let a, cond_a = tr_term ~state ~local_state:(no_pol local_state) a in
            let b, cond_b = tr_term ~state ~local_state b in
            let c, cond_c = tr_term ~state ~local_state c in
            add_conds local_state.pol
              (T.app_builtin B.Ite [a;b;c])
              (List.flatten [cond_a; cond_b; cond_c])
        | B.Eq, [a;b] ->
            let a, cond_a = tr_term ~state ~local_state a in
            let b, cond_b = tr_term ~state ~local_state b in
            add_conds local_state.pol
              (T.app_builtin B.Eq [a;b])
              (List.append cond_a cond_b)
        | B.DataTest _, _
        | B.DataSelect (_,_), _ -> t, []
        | B.Not,_
        | B.Imply,_
        | B.Ite,_
        | B.Eq,_ -> assert false
        end
    | TI.Bind (TI.Forall,v,t) ->
        begin match 
        let t', conds = tr_term ~state ~local_state t in
        T.forall v t',  List.map (T.forall v) conds
    | TI.Bind (TI.Exists,v,t) ->
        let t, cond = tr_term ~state ~local_state t in
        add_conds local_state.pol (T.exists v t) cond
    | TI.Bind (TI.Fun,_,_) -> fail_tr_ t "translation of λ impossible"
    | TI.Let (v,t,u) ->
        let t, c1 = tr_term ~state ~local_state t in
        let u, c2 = tr_term ~state ~local_state u in
        T.let_ v t u, List.append c1 c2
    | TI.Match (t, l) ->
        let t, ct = tr_term ~state ~local_state t in
        let conds' = ref [] in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let rhs, conds = tr_term ~state ~local_state rhs in
            l := conds @ !l;
            vars,rhs
          ) l
        in
        T.match_with t l, ct @ !l
    | TI.Bind (TI.TyForall,_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, []

  let tr_term_top ~state ~local_state t = fst (tr_term ~state ~local_state t)

  (* translate a statement *)
  let tr_statement ~state st =
    let local_state = {
      defining=None;
      pol=Pos;
      new_tys=[];
    } in
    (* update signature *)
    state.sigma <- Sig.add_statement ~sigma:state.sigma st;
    let info = Stmt.info st in
    (* try to update the statement *)
    try
      let st' = match Stmt.view st with
        | Stmt.Decl _ -> st (* no type declaration changes *)
        | Stmt.TyDef (_,_) -> st (* no (co) data changes *)
        | Stmt.Axiom l ->
            begin match l with
            | Stmt.Axiom_rec l ->
                (* TODO: declare abstract type + projectors first *)
                (* transform each axiom, considering case_head as rec. defined *)
                let l = List.map
                  (fun case ->
                    let local_state = {local_state with
                      defining=Some case.Stmt.case_head;
                    } in
                    let axioms' =
                      List.map (tr_term_top ~state ~local_state) case.Stmt.case_axioms
                    in
                    {case with Stmt.case_axioms=axioms'}
                  ) l
                in
                Stmt.axiom_rec ~info l
            | Stmt.Axiom_spec l ->
                let l = List.map
                  (fun case ->
                    let axioms' =
                      List.map (tr_term_top ~state ~local_state) case.Stmt.case_axioms
                    in
                    {case with Stmt.case_axioms=axioms'}
                  ) l
                in
                Stmt.axiom_spec ~info l
            | Stmt.Axiom_std l ->
                let l = List.map (tr_term_top ~state ~local_state) l in
                Stmt.axiom ~info l
            end
        | Stmt.Goal g ->
            Stmt.goal ~info (tr_term_top ~state ~local_state g)
      in
      (* put [st'] after the new statements, because those are type declarations *)
      List.rev (st' :: local_state.side_statements)
    with TranslationFailed (t, msg) ->
      (* could not translate, keep old statement *)
      NunUtils.debugf ~section 1
        "[<2>recursion elimination in@ @[%a@]@ failed on subterm @[%a@]:@ %s@]"
          (fun k -> k (Stmt.print PrintT.print PrintT.print_ty) st PrintT.print t msg);
      [st]

  let elim_recursion pb =
    let state = create_state() in
    let pb' = NunProblem.flat_map_statements ~f:(tr_statement ~state) pb in
    pb', state.decode

  let decode_term ~state:_ t = t (* TODO *)

  let decode_model ~state m =
    NunModel.map ~f:(decode_term ~state) m
end

let pipe_with (type a) ~decode ~print
(module T : NunTerm_ho.S with type t = a)
=
  let module DoIt = Make(T) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T) in
      [Format.printf "@[<v2>after elimination of recursion: %a@]@."
        (NunProblem.print ~pty_in_app:P.print_in_app P.print P.print_ty)]
    else []
  in
  NunTransform.make1
    ~on_encoded
    ~name:"recursion_elim"
    ~encode:(fun p ->
      let p, state = DoIt.elim_recursion p in
      p, state
      (* TODO mangling of types, as an option *)
    )
    ~decode:(fun state x ->
      let decode_term = DoIt.decode_term ~state in
      decode ~decode_term x
    )
    ()

let pipe (type a) ~print (t : (module NunTerm_ho.S with type t = a)) =
  let decode ~decode_term = NunModel.map ~f:decode_term in
  pipe_with ~print t ~decode
