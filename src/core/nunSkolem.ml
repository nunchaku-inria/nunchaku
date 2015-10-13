
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

  type state

  val create : ?prefix:string -> unit -> state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val convert_term : state:state -> T1.t -> T2.t * (id * T2.ty) list
  (** [convert_term ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> state -> unit

  val convert_problem :
    state:state ->
    (T1.t, T1.ty) NunProblem.t ->
    (T2.t, T2.ty) NunProblem.t

  val decode_model :
    state:state -> T2.t NunProblem.Model.t -> T2.t NunProblem.Model.t
end

module Make(T1 : NunTerm_ho.VIEW)(T2 : NunTerm_ho.S)
  : S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  module P1 = NunTerm_ho.Print(T1)
  module P2 = NunTerm_ho.Print(T2)
  module U1 = NunTerm_intf.Util(T1)
  module Subst = NunVar.Subst(T1)
  module Stmt = NunProblem.Statement
  module Conv = NunTerm_ho.Convert(T1)(T2)

  type new_sym = {
    sym_defines : T1.t; (* what is the formula represented by the symbol *)
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

  let convert_term_ ~state t =
    let rec aux ~env t = match T1.view t with
      | TI.Builtin b -> T2.builtin b
      | TI.Const id -> T2.const id
      | TI.Var v ->
          begin match Subst.find ~subst:env.subst v with
          | None -> T2.var (aux_var ~env v)
          | Some t -> t
          end
      | TI.App (f,l) ->
          T2.app (aux ~env f) (List.map (aux ~env) l)
      | TI.Fun (v,t) ->
          enter_var_ ~env v
            (fun env v -> T2.fun_ v (aux ~env t))
      | TI.Forall (v,t) ->
          enter_var_ ~env v
            (fun env v -> T2.forall v (aux ~env t))
      | TI.Exists (v,t') ->
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
            ID.print_no_id skolem_id P2.print_ty ty P1.print t;
          (* convert [t] and replace [v] with [skolem] in it *)
          let env = env_bind ~env v skolem in
          aux ~env t'
      | TI.Let (v,t,u) ->
          let t = aux ~env t in
          enter_var_ ~env v (fun env v -> T2.let_ v t (aux ~env u))
      | TI.Ite (a,b,c) -> T2.ite (aux ~env a)(aux ~env b)(aux ~env c)
      | TI.Eq (a,b) -> T2.eq (aux ~env a) (aux ~env b)
      | TI.TyKind -> T2.ty_kind
      | TI.TyType -> T2.ty_type
      | TI.TyBuiltin b -> T2.ty_builtin b
      | TI.TyArrow (a,b) -> T2.ty_arrow (aux ~env a)(aux ~env b)
      | TI.TyForall (v,t) ->
          enter_var_ ~env v (fun env v -> T2.ty_forall v (aux ~env t))
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

  let convert_term ~state t =
    let t' = convert_term_ ~state t in
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
          (fun (id,s) -> Stmt.decl id s.sym_ty)
          l
      )
      ~term:(convert_term_ ~state)
      ~ty:(convert_term_ ~state)
      pb

  let fpf = Format.fprintf

  let print_state out st =
    let pp_sym out (id,s) =
      fpf out "@[<2>%a: %a@ standing for `@[%a@]`@]"
        ID.print_no_id id P2.print_ty s.sym_ty P1.print s.sym_defines
    in
    fpf out "@[<2>skolem table {@,%a@]@,}"
      (CCFormat.seq pp_sym) (ID.Tbl.to_seq st.tbl)

  let epsilon = ID.make ~name:"_witness_of"

  let decode_model ~state m =
    m |> List.map
        (fun (t,u) -> match T2.view t with
          | TI.Const id ->
              (* if [id] is a Skolem symbol, use an epsilon to display the
                existential formula it is the witness of *)
              begin try
                let sym = ID.Tbl.find state.tbl id in
                let f = Conv.convert sym.sym_defines in
                T2.app (T2.const epsilon) [f], u
              with Not_found ->
                t, u
              end
          | _ -> t, u
        )
end

let pipe (type a)(type b) ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let module S = Make(T1)(T2) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T2) in
      [Format.printf "@[<2>after Skolemization:@ %a@]@."
        (NunProblem.print P.print P.print_ty)]
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
    ~decode:(fun state m -> S.decode_model ~state m)
    ()

