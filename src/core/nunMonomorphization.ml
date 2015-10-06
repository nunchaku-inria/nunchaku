
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

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

  type state = unit (* TODO *)

  let encode_problem p = assert false (* TODO use fold + build *)

  let decode_model m = assert false (* TODO *)
end


