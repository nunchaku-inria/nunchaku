
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Infinite Types} *)

open Nunchaku_core

type term = Term.t

type decode_state

val name : string

val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   (term,term) Problem.Res.t, (term,term) Problem.Res.t
  ) Transform.t
(** Pipeline component *)

val pipe_with :
  decode:(decode_state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t, 'c, 'd
  ) Transform.t
(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
