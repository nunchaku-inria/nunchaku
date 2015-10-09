
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

module ID = NunID
module TI = NunTerm_intf
module Var = NunVar

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  type state

  val create : unit -> state

  val convert_term : state:state -> T1.t -> T2.t

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

  type state = unit (* TODO *)

  let create () = ()

  (* TODO skolemize existential quantifiers *)
  let convert_term ~state t =
    let rec aux t = match T1.view t with
      | TI.Builtin b -> T2.builtin b
      | TI.Const id -> T2.const id
      | TI.Var v -> T2.var (aux_var v)
      | TI.App (f,l) -> T2.app (aux f) (List.map aux l)
      | TI.Fun (v,t) -> T2.fun_ (aux_var v) (aux t)
      | TI.Forall (v,t) -> T2.forall (aux_var v) (aux t)
      | TI.Exists (v,t) -> T2.exists (aux_var v) (aux t)
      | TI.Let (v,t,u) -> T2.let_ (aux_var v) (aux t)(aux u)
      | TI.Ite (a,b,c) -> T2.ite (aux a)(aux b)(aux c)
      | TI.Eq (a,b) -> T2.eq (aux a)(aux b)
      | TI.TyKind -> T2.ty_kind
      | TI.TyType -> T2.ty_type
      | TI.TyBuiltin b -> T2.ty_builtin b
      | TI.TyArrow (a,b) -> T2.ty_arrow (aux a)(aux b)
      | TI.TyForall (v,t) -> T2.ty_forall (aux_var v) (aux t)
      | TI.TyMeta _ -> assert false
    and aux_var = Var.update_ty ~f:aux in
    aux t

  let convert_problem ~state pb =
    NunProblem.map
      ~term:(convert_term ~state)
      ~ty:(convert_term ~state)
      pb

  let decode_model ~state m = m (* TODO *)
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
    ~encode:(fun pb ->
      let state = S.create() in
      let pb = S.convert_problem ~state pb in
      pb, state
    )
    ~decode:(fun state m -> S.decode_model ~state m)
    ()

