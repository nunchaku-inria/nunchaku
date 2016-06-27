
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

module T = TermInner.Default

val name : string

type term = T.t

val elim :
  (term, term) Problem.t ->
  (term, term) Problem.t

val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'c) Transform.t
