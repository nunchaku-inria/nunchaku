
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(* {1 TPTP Printer} *)

type 'a printer = Format.formatter -> 'a -> unit

type term = NunUntypedAST.term
type form= NunUntypedAST.term
type model = term NunProblem.Model.t

let print_term out t = assert false

let print_form out t = assert false

let print_model out t = assert false


