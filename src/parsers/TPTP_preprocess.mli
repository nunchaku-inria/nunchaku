(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP Preprocessor}

    This file preprocesses TPTP problems to adapt them for Nunchaku:

    {ul
    {- declare TPTP primitives}
    {- declare symbols that are not explicitely declared}
    {- add "$i" to variables that have no type}
    }
*)

open Nunchaku_core

type 'a or_error = ('a, string) CCResult.t

val preprocess_exn :
  UntypedAST.statement Iter.t ->
  UntypedAST.statement CCVector.ro_vector

val preprocess :
  UntypedAST.statement Iter.t ->
  UntypedAST.statement CCVector.ro_vector or_error
