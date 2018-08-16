
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Elimination of Higher-Order Functions}

    Encode partial applications and higher-order applications *)

open Nunchaku_core

val name : string

type term = Term.t
type decode_state

val elim_hof :
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
  ?on_decoded:(('d -> unit) list) ->
  decode:(decode_state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'd
  ) Transform.t
