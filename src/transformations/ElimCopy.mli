
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

val name : string

type term = Term.t
type ty = term

type decode_state

val elim :
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val pipe :
  print:bool ->
  check:bool ->
  ((term, ty) Problem.t,
   (term, ty) Problem.t,
   (term, ty) Problem.Res.t,
   (term, ty) Problem.Res.t) Transform.t
