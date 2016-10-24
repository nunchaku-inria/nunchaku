
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

open Nunchaku

type term = TermInner.Default.t

val name : string

exception Error of string

val uniq_eqns_pb :
  (term, term) Problem.t ->
  (term, term) Problem.t

(** Pipeline component *)
val pipe :
  decode:('c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'd) Transform.t
