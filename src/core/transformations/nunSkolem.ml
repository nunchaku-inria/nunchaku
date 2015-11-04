
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

module ID = NunID
module TI = NunTerm_intf
module Var = NunVar

type id = NunID.t

let section = NunUtils.Section.make "skolem"

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S
    with type invariant_poly = T1.invariant_poly
    and type invariant_meta = T1.invariant_meta

  type state

  val create : ?prefix:string -> unit -> state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : T1.t -> T2.t
  (** Put term in negation normal form *)

  val skolemize : state:state -> T2.t -> T2.t * (id * T2.ty) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> state -> unit

  val convert_problem :
    state:state ->
    (T1.t, T1.ty, 'inv) NunProblem.t ->
    (T2.t, T2.ty, 'inv) NunProblem.t

  val find_id_def : state:state -> id -> T2.t option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:state -> T2.t NunModel.t -> T2.t NunModel.t
end

module Make(T1 : NunTerm_ho.VIEW)(T2 :
  NunTerm_ho.S
  with type invariant_poly = T1.invariant_poly
  and type invariant_meta = T1.invariant_meta
) : S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  module P2 = NunTerm_ho.Print(T2)
  module Subst = NunVar.Subst(T2)
  module Stmt = NunStatement

  type new_sym = {
    sym_defines : T2.t; (* what is the formula represented by the symbol *)
    sym_ty : T2.ty; (* type of the symbol *)
  }

  type state = {
    tbl: new_sym ID.Tbl.t; (* skolem -> quantified form *)
    prefix:string; (* prefix for Skolem symbols *)
    mutable name : int;
    mutable new_sym: (id * new_sym) list; (* list of newly defined symbols *)
  }

  let create ?(prefix="nun_sk_") () = {
    tbl=ID.Tbl.create 32;
    prefix;
    name=0;
    new_sym=[];
  }

  type env = {
    vars: T2.ty Var.t list;  (* variables on the path *)
    subst: T2.t Subst.t; (* substitution for existential variables *)
  }

  let env_bind ~env v t =
    { env with subst=Subst.add ~subst:env.subst v t }

  let env_add_var ~env v =
    { env with vars=v :: env.vars }

  let new_sym ~state =
    let n = state.name in
    state.name <- n+1;
    ID.make ~name:(state.prefix ^ string_of_int n)

  module B = NunBuiltin.T
  let mk_true = T2.builtin B.True
  let mk_false = T2.builtin B.False
  let mk_not a = T2.app_builtin B.Not [a]
  let mk_and a b = T2.app_builtin B.And [a;b]
  let mk_or a b = T2.app_builtin B.Or [a;b]
  let mk_ite a b c = T2.app_builtin B.Ite [a;b;c]

  (* first, negation normal form *)
  let rec nnf t = match T1.view t with
    | TI.Const id -> T2.const id
    | TI.Var v -> T2.var (nnf_var_ v)
    | TI.App (f,l) -> T2.app (nnf f) (List.map nnf l)
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | B.True, _ -> mk_true
        | B.False, _ -> mk_false
        | B.Or, _
        | B.And, _
        | B.Ite, _
        | B.Eq, _ -> T2.app_builtin b (List.map nnf l)
        | B.Imply, [a;b] -> mk_or (nnf_neg a) (nnf b)
        | B.Equiv, [a;b] -> (* a => b & b => a *)
            mk_and (mk_or (nnf_neg a) (nnf b)) (mk_or (nnf_neg b) (nnf a))
        | B.Not, [f] -> nnf_neg f
        | _ -> assert false
        end
    | TI.Bind (k,v,t) -> T2.mk_bind k (nnf_var_ v) (nnf t)
    | TI.Let (v,t,u) ->
        T2.let_ (nnf_var_ v) (nnf t) (nnf u)
    | TI.Match (t,l) ->
        T2.match_with (nnf t)
          (ID.Map.map (fun (vars,rhs) -> List.map nnf_var_ vars,nnf rhs) l)
    | TI.TyBuiltin b -> T2.ty_builtin b
    | TI.TyArrow (a,b) -> T2.ty_arrow (nnf a) (nnf b)
    | TI.TyMeta _ -> assert false

  (* negation + negation normal form *)
  and nnf_neg t = match T1.view t with
    | TI.Const id -> mk_not (T2.const id)
    | TI.Var v -> mk_not (T2.var (nnf_var_ v))
    | TI.App (f,l) -> mk_not (T2.app (nnf f) (List.map nnf l))
    | TI.AppBuiltin (b,l) ->
        begin match b, l with
        | B.True, _ -> mk_false
        | B.False, _ -> mk_true
        | B.Or, l -> T2.app_builtin B.And (List.map nnf_neg l)
        | B.And, l -> T2.app_builtin B.Or (List.map nnf_neg l)
        | B.Ite, [a;b;c] ->
            mk_ite (nnf a) (nnf_neg b) (nnf_neg c)
        | B.Eq, _ -> mk_not (T2.app_builtin b (List.map nnf l))
        | B.Imply, [a;b] ->
            mk_and (nnf a) (nnf_neg b)  (* a & not b *)
        | B.Equiv, [a;b] -> (* not a & b | not b & a *)
            mk_or (mk_and (nnf_neg a) (nnf b)) (mk_and (nnf_neg b) (nnf a))
        | B.Not, [f] -> nnf f (* not not f -> f *)
        | _ -> assert false
        end
    | TI.Bind (TI.Forall, v,t) -> T2.exists (nnf_var_ v) (nnf_neg t)
    | TI.Bind (TI.Exists, v,t) -> T2.forall (nnf_var_ v) (nnf_neg t)
    | TI.Bind (TI.Fun,_,_) -> failwith "cannot skolemize function"
    | TI.Bind (TI.TyForall,_,_) -> failwith "cannot skolemize `ty_forall`"
    | TI.Let (v,t,u) ->
        T2.let_ (nnf_var_ v) (nnf t) (nnf u)
    | TI.Match _ ->
        mk_not (nnf t)
    | TI.TyBuiltin b -> T2.ty_builtin b
    | TI.TyArrow (a,b) -> T2.ty_arrow (nnf a) (nnf b)
    | TI.TyMeta _ -> assert false

  and nnf_var_ v = Var.update_ty v ~f:nnf

  let skolemize_ ~state t =
    (* recursive traversal *)
    let rec aux ~env (t:T2.t) = match T2.view t with
      | TI.Const id -> T2.const id
      | TI.Var v ->
          let t = match Subst.find ~subst:env.subst v with
            | None -> T2.var (aux_var ~env v)
            | Some t -> t
          in
          t
      | TI.AppBuiltin (b,l) ->
          begin match b, l with
          | B.True, _
          | B.False, _ -> t
          | B.Not, [f] -> mk_not (aux ~env f)
          | B.Or, _
          | B.And, _
          | B.Ite, _
          | B.Eq, _ ->
              T2.app_builtin b (List.map (aux ~env) l)
          | B.Imply, _
          | B.Equiv, _ -> assert false
          | _ -> assert false
          end
      | TI.App (f,l) ->
          T2.app (aux ~env f) (List.map (aux ~env) l)
      | TI.Bind (TI.TyForall, v, t) ->
          enter_var_ ~env v
            (fun env v -> T2.mk_bind TI.TyForall v (aux ~env t))
      | TI.Bind ((TI.Fun | TI.Forall) as b, v, t) ->
          enter_var_ ~env v
            (fun env v -> T2.mk_bind b v (aux ~env t))
      | TI.Bind (TI.Exists, v, t') ->
          (* type of Skolem function *)
          let ty_ret = aux ~env (Var.ty v) in
          let ty_args = List.map Var.ty env.vars in
          let ty = List.fold_right T2.ty_arrow ty_args ty_ret in
          (* create new skolem function *)
          let skolem_id = new_sym ~state in
          let skolem = T2.app (T2.const skolem_id) (List.map T2.var env.vars) in
          let new_sym = { sym_defines=t; sym_ty=ty } in
          ID.Tbl.add state.tbl skolem_id new_sym;
          state.new_sym <- (skolem_id, new_sym):: state.new_sym;
          NunUtils.debugf ~section 2
            "@[<2>new Skolem symbol `%a :@ @[%a@]` standing for@ @[`%a`@]@]"
            (fun k-> k ID.print_no_id skolem_id P2.print_ty ty P2.print t);
          (* convert [t] and replace [v] with [skolem] in it *)
          let env = env_bind ~env v skolem in
          aux ~env t'
      | TI.Let (v,t,u) ->
          let t = aux ~env t in
          enter_var_ ~env v (fun env v -> T2.let_ v t (aux ~env u))
      | TI.Match (t, l) ->
          let t = aux ~env t in
          let l = ID.Map.map
            (fun (vars,rhs) ->
              let env, vars' = NunUtils.fold_map
                (fun env v ->
                  let v' = aux_var ~env v in
                  let env = env_add_var ~env v' in
                  env, v'
                ) env vars
              in
              vars', aux ~env rhs
            ) l
          in
          T2.match_with t l
      | TI.TyBuiltin b -> T2.ty_builtin b
      | TI.TyArrow (a,b) -> T2.ty_arrow (aux ~env a) (aux ~env b)
      | TI.TyMeta _ -> assert false

    and aux_var ~env = Var.update_ty ~f:(aux ~env)

    and enter_var_ ~env v f =
      let v' = aux_var ~env v in
      let env = env_add_var ~env v' in
      f env v'
    in
    let env = {
      vars=[];
      subst=Subst.empty;
    } in
    aux ~env t

  let skolemize ~state t =
    let t' = skolemize_ ~state t in
    (* clear list of new symbols *)
    let l = state.new_sym in
    state.new_sym <- [];
    t', List.map (fun (id,s) -> id,s.sym_ty) l

  let convert_problem ~state pb =
    NunProblem.map_with
      ~before:(fun () ->
        let l = state.new_sym in
        state.new_sym <- [];
        List.map
          (fun (id,s) -> Stmt.decl ~info:Stmt.info_default id s.sym_ty)
          l
      )
      ~term:(fun t -> skolemize_ ~state (nnf t))
      ~ty:(fun t -> skolemize_ ~state (nnf t))
      pb

  let fpf = Format.fprintf

  let print_state out st =
    let pp_sym out (id,s) =
      fpf out "@[<2>%a: %a@ standing for `@[%a@]`@]"
        ID.print_no_id id P2.print_ty s.sym_ty P2.print s.sym_defines
    in
    fpf out "@[<2>skolem table {@,%a@]@,}"
      (CCFormat.seq pp_sym) (ID.Tbl.to_seq st.tbl)

  let epsilon = ID.make ~name:"_witness_of"

  let find_id_def ~state id =
    (* if [id] is a Skolem symbol, use an epsilon to display the
      existential formula it is the witness of *)
    try
      let sym = ID.Tbl.find state.tbl id in
      let f = sym.sym_defines in
      Some (T2.app (T2.const epsilon) [f])
    with Not_found -> None

  let decode_model ~state m =
    m |> List.map
        (fun (t,u) -> match T2.view t with
          | TI.Const id ->
              begin match find_id_def ~state id with
                | None -> t, u
                | Some t' -> t', u
              end
          | _ -> t, u
        )
end

let pipe_with (type a)(type b) ~decode ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let module S = Make(T1)(T2) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T2) in
      [Format.printf "@[<v2>after Skolemization: %a@]@."
        (NunProblem.print
          ~pt_in_app:P.print_in_app ~pty_in_app:P.print_in_app
          P.print P.print_ty)]
    else []
  in
  NunTransform.make1
    ~name:"skolem"
    ~on_encoded
    ~print:S.print_state
    ~encode:(fun pb ->
      let state = S.create() in
      let pb = S.convert_problem ~state pb in
      pb, state
    )
    ~decode:(fun state x ->
      decode ~find_id_def:(S.find_id_def ~state) x
    )
    ()

let pipe (type a)(type b) ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let decode ~find_id_def m =
    m |> List.map
        (fun (t,u) -> match T2.view t with
          | TI.Const id ->
              begin match find_id_def id with
                | None -> t, u
                | Some t' -> t', u
              end
          | _ -> t, u
        )
  in
  pipe_with ~decode ~print (module T1)(module T2)
