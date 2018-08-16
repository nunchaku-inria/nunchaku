
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lift Undefined}

    Individually name and declare every "undefined" occurring in
    the problem.
    The name "lifting" comes from the similar transformation of "lambda lifting";
    we "lift" undefined terms at the top-level.
*)

open Nunchaku_core

type term = Term.t

val name : string

type decode_state

val encode_pb :
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val decode_model :
  decode_state -> (term, term) Model.t -> (term, term) Model.t

val pipe :
  print:bool ->
  check:bool ->
  ((term,term) Problem.t,
   (term,term) Problem.t,
   (term,term) Problem.Res.t, (term,term) Problem.Res.t
  ) Transform.t

