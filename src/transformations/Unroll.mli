
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unrolling of (Co)inductive Predicates} *)

open Nunchaku_core

type term = TermInner.Default.t
type decode_state

val name : string

val unroll :
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val decode_model :
  state:decode_state -> (term,term) Model.t -> (term,term) Model.t

(** Pipeline component *)
val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   (term, term) Problem.Res.t, (term, term) Problem.Res.t) Transform.t

(** Generic Pipe Component *)
val pipe_with :
  ?on_decoded:(('d -> unit) list) ->
  decode:(decode_state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'd
  ) Transform.t
