
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Prelude}

    A list of declarations that is pre-pended to any input problem,
    with some builtin functions *)

val choice : ID.t
val unique : ID.t
val unique_unsafe : ID.t

val decls : UntypedAST.statement list



