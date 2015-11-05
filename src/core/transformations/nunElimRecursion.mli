
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

type invariant = <poly:NunMark.monomorph; meta:NunMark.without_meta>

type 't decode_state

val elim_recursion :
  build:('t, invariant) NunTerm_ho.build ->
  ('t, 't, NunMark.linear) NunProblem.t ->
  ('t, 't, NunMark.linear) NunProblem.t * 't decode_state

val decode_term : state:'t decode_state -> 't -> 't

val decode_model : state:'t decode_state -> 't NunModel.t -> 't NunModel.t

(** Pipeline component *)
val pipe :
  print:bool ->
  build:('t, invariant) NunTerm_ho.build ->
  (('t, 't, NunMark.linear) NunProblem.t,
    ('t, 't, NunMark.linear) NunProblem.t,
    't NunModel.t, 't NunModel.t) NunTransform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  decode:(decode_term:('t -> 't) -> 'c -> 'd) ->
  print:bool ->
  build:('t, invariant) NunTerm_ho.build ->
  (('t, 't, NunMark.linear) NunProblem.t,
    ('t, 't, NunMark.linear) NunProblem.t,
    'c, 'd
  ) NunTransform.t


