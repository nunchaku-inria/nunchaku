(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

type 'a printer = Format.formatter -> 'a -> unit

type term = NunUntypedAST.term
type form= NunUntypedAST.term
type model = term NunProblem.Model.t

val print_term : term printer

val print_form : form printer

val print_model : model printer




