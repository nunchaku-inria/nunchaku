
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer} *)

val token : Lexing.lexbuf -> Parser.token

(** {2 Utils} *)

include Parsing_utils.S

