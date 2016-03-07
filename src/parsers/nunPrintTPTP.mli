(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

open Nunchaku_core

type 'a printer = Format.formatter -> 'a -> unit

exception Error of string

module Make(T : TermInner.S) : sig
  type term = T.t
  type form = T.t
  type ty = T.t
  type model = (term, ty) Model.t

  val print_term : term printer

  val print_form : form printer

  val print_model : model printer
end

