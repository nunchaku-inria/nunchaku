
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Quantifiers}

    Remove some quantifiers depending on their polarity.

    Positive existentials are replaced by fresh constants declared at
    top-level, negative ones are replaced by [false].
    *)

open Nunchaku_core

type term = TermInner.Default.t

type to_elim =
  | Elim_quant_data (* remove quantifiers on datatypes *)
  | Elim_quant_fun (* remove quantifiers on functions *)
  | Elim_eq_fun (* remove equality on functions *)

type mode = to_elim list

val pp_to_elim : to_elim CCFormat.printer
val pp_mode : mode CCFormat.printer

val name : string

type decode_state

val encode_pb :
  mode:mode ->
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val decode_model :
  decode_state -> (term, term) Model.t -> (term, term) Model.t

val pipe :
  print:bool ->
  check:bool ->
  mode:mode ->
  ((term,term) Problem.t,
   (term,term) Problem.t,
   (term,term) Problem.Res.t, (term,term) Problem.Res.t
  ) Transform.t
