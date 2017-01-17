
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4.
    It encodes recursive functions as axioms, with a quantification over
    an uninterpreted abstraction type. *)

open Nunchaku_core

val name : string

type term = TermInner.Default.t
type decode_state

val elim_recursion :
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val decode_model :
  state:decode_state ->
  (term, term) Model.t ->
  (term, term) Model.t

(** Pipeline component *)
val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   (term, term) Problem.Res.t,
   (term, term) Problem.Res.t) Transform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  ?on_decoded:('d -> unit) list ->
  decode:(decode_state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'd
  ) Transform.t

