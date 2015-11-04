
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

module Make(T : NunTerm_ho.S
  with type invariant_poly=NunMark.monomorph
  and type invariant_meta=NunMark.without_meta)
: sig

  type decode_state

  val elim_recursion :
    (T.t, T.ty, NunMark.linear) NunProblem.t ->
    (T.t, T.ty, NunMark.linear) NunProblem.t * decode_state

  val decode_term : state:decode_state -> T.t -> T.t

  val decode_model : state:decode_state -> T.t NunModel.t -> T.t NunModel.t
end

(** Pipeline component *)
val pipe :
  print:bool ->
  (module NunTerm_ho.S with type t = 'a
    and type invariant_poly=NunMark.monomorph
    and type invariant_meta=NunMark.without_meta) ->
  (('a, 'a, NunMark.linear) NunProblem.t,
    ('a, 'a, NunMark.linear) NunProblem.t,
    'a NunModel.t, 'a NunModel.t) NunTransform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  decode:(decode_term:('a -> 'a) -> 'c -> 'd) ->
  print:bool ->
  (module NunTerm_ho.S with type t = 'a
    and type invariant_poly=NunMark.monomorph
    and type invariant_meta=NunMark.without_meta) ->
  (('a, 'a, NunMark.linear) NunProblem.t,
    ('a,'a, NunMark.linear) NunProblem.t,
    'c, 'd
  ) NunTransform.t


