
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Guards}

    This transformation removes "assuming" and "asserting" constructs and
    replaces them by boolean guards and assertions *)

open Nunchaku_core

module T = TermInner.Default

type term = T.t

val name : string

val encode_pb : (term, term) Problem.t -> (term, term) Problem.t

(** Pipeline component *)
val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
    (term, term) Problem.t,
    'ret, 'ret) Transform.t
