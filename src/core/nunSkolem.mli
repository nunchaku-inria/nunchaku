
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

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

val pipe :
  print:bool ->
  (module NunTerm_ho.VIEW with type t = 'a) ->
  (module NunTerm_ho.S with type t = 'b) ->
  (('a,'a) NunProblem.t, ('b,'b) NunProblem.t,
    'b NunProblem.Model.t, 'b NunProblem.Model.t
  ) NunTransform.t


