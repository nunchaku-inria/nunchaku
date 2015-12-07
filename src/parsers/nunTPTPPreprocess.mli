
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP Preprocessor}

  This file preprocesses TPTP problems to adapt them for Nunchaku:

  {ul
  {- declare TPTP primitives}
  {- declare symbols that are not explicitely declared}
  {- add "$i" to variables that have no type}
  }
*)

type 'a or_error = [`Ok of 'a | `Error of string]

val preprocess_exn :
  UntypedAST.statement Sequence.t ->
  (UntypedAST.statement, CCVector.ro) CCVector.t

val preprocess :
  UntypedAST.statement Sequence.t ->
  (UntypedAST.statement, CCVector.ro) CCVector.t or_error
