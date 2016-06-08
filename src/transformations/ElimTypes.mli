
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Simple Types} *)

open Nunchaku_core

module TI = TermInner
module T = TermInner.Default

val name : string

type state

val transform_pb :
  (T.t, T.t) Problem.t ->
  (T.t, T.t) Problem.t * state

val decode_model :
  state:state -> (T.t,T.t) Model.t -> (T.t,T.t) Model.t

val pipe :
  print:bool ->
  check:bool ->
  ((T.t,T.t) Problem.t,
   (T.t,T.t) Problem.t,
    (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
  ) Transform.t

val pipe_with :
  ?on_decoded:('d -> unit) list ->
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((T.t,T.t) Problem.t,
   (T.t,T.t) Problem.t, 'c, 'd
  ) Transform.t
