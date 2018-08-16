
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Merge Multiple Equations into One} *)

(** The goal is to transform a problem where definitions have
    multiple equations (à la Haskell or Isabelle/HOL),
    into a problem where each ID has a single equations
*)

open Nunchaku_core

type term = Term.t

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
