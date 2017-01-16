
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Simple Types} *)

open Nunchaku_core

type term = TermInner.Default.t
type state

val name : string

val transform_pb :
  (term, term) Problem.t ->
  (term, term) Problem.t * state

val decode_model :
  state:state -> (term,term) Model.t -> (term,term) Model.t

val pipe :
  print:bool ->
  check:bool ->
  ((term,term) Problem.t,
   (term,term) Problem.t,
   (term,term) Problem.Res.t, (term,term) Problem.Res.t
  ) Transform.t

val pipe_with :
  ?on_decoded:('d -> unit) list ->
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term,term) Problem.t,
   (term,term) Problem.t, 'c, 'd
  ) Transform.t
