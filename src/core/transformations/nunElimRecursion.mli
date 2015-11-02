
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

module Make(T : NunTerm_ho.S) : sig

  type decode_state

  val elim_recursion :
    (T.t, T.ty) NunProblem.t ->
    (T.t, T.ty) NunProblem.t * decode_state

  val decode_term : state:decode_state -> T.t -> T.t

  val decode_model : state:decode_state -> T.t NunModel.t -> T.t NunModel.t
end

(** Pipeline component *)
val pipe :
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t,
    'a NunModel.t, 'a NunModel.t) NunTransform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  decode:(decode_term:('a -> 'a) -> 'c -> 'd) ->
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t, 'c, 'd) NunTransform.t


