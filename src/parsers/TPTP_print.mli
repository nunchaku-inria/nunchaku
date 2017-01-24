(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

open Nunchaku_core

type 'a printer = Format.formatter -> 'a -> unit

exception Error of string

type term = TermInner.Default.t
type form = term
type ty = term
type model = (term, ty) Model.t

val pp_term : term printer

val pp_form : form printer

val pp_model : model printer
