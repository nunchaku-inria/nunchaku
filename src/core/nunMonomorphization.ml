
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module T1I = NunTerm_typed

module type S = sig
  module T1 : NunTerm_typed.VIEW
  module T2 : NunTerm_ho.S

  (** Useful for decoding *)
  type state

  val encode_problem :
    (T1.t,T1.ty) NunProblem.t ->
    (T2.t,T2.ty) NunProblem.t * state
  (** Monomorphize the problem, and save enough context in [state] for
      decoding to work *)

  val decode_model : state -> T2.t NunProblem.Model.t -> T2.t NunProblem.Model.t
  (** Stay in the same term representation, but de-monomorphize *)
end

module Make(T1 : NunTerm_typed.VIEW)(T2 : NunTerm_ho.S)
  : S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  type state = {
    rev: T2.t ID.Tbl.t; (* new identifier -> monomorphized term *)
  }

  let create_st_ () = {
    rev=ID.Tbl.create 64;
  }

  (* TODO: the encoding itself
      - detect polymorphic functions
      - specialize them on some ground type (skolem?)
      - declare f_alpha : (typeof f) applied to alpha
      - add (f alpha) -> f_alpha in [rev]
      - rewrite (f alpha) into f_alpha everywhere
  *)

  (* make encoding functions for terms and types *)
  let mk_ ~st:_ =
    let rec aux t = match T1.view t with
      | T1I.Builtin b -> T2.builtin b
      | T1I.Const c -> T2.const c
      | T1I.Var v -> T2.var (aux_var v)
      | T1I.App (f,l) -> T2.app (aux f) (List.map aux l)
      | T1I.Fun (v,t) -> T2.fun_ (aux_var v) (aux t)
      | T1I.Forall (v,t) -> T2.forall (aux_var v) (aux t)
      | T1I.Exists (v,t) -> T2.exists (aux_var v) (aux t)
      | T1I.Let (v,t,u) -> T2.let_ (aux_var v) (aux t) (aux u)
      | T1I.TyKind -> (T2.ty_kind :> T2.t)
      | T1I.TyType -> (T2.ty_type :> T2.t)
      | T1I.TyMeta _ -> failwith "Mono.encode: type meta-variable"
      | T1I.TyBuiltin b -> (T2.ty_builtin b :> T2.t)
      | T1I.TyArrow (a,b) -> (T2.ty_arrow (aux a) (aux b) :> T2.t)
      | T1I.TyForall (v,t) -> (T2.ty_forall (aux_var v) (aux t) :> T2.t)
    and aux_var = Var.update_ty ~f:aux
    in
    aux, aux

  let encode_problem p =
    let st = create_st_ () in
    let term, ty = mk_ ~st in
    let p' = NunProblem.map ~term ~ty p in
    p', st

  (* TODO:
    - decode  f_alpha into (f alpha)
  *)

  let decode_model _st m = m (* TODO *)
end


