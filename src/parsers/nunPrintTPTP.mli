(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

open Nunchaku_core

type 'a printer = Format.formatter -> 'a -> unit

type term = UntypedAST.term
type form = UntypedAST.term
type ty = UntypedAST.ty
type model = (term, ty) Model.t

val print_term : term printer

val print_form : form printer

val print_model : model printer




