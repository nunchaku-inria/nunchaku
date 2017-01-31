
(* This file is free software. See file "license" for more details. *)

(** {1 Lexer for TIP} *)

{
  open Nunchaku_core
  module A = Tip_ast
  module Loc = Location
  open Tip_parser (* for tokens *)

}

let printable_char = [^ '\n']
let comment_line = ';' printable_char*

let sym = [^ '"' '(' ')' '\\' ' ' '\t' '\r' '\n']

let ident = sym+

let quoted = '"' ([^ '"'] | '\\' '"')* '"'

rule token = parse
  | eof { EOI }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | comment_line { token lexbuf }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | "Bool" { BOOL }
  | "true" { TRUE }
  | "false" { FALSE }
  | "or" { OR }
  | "and" { AND }
  | "not" { NOT }
  | "distinct" { DISTINCT }
  | "ite" { IF }
  | "as" { AS }
  | "match" { MATCH }
  | "case" { CASE }
  | "default" { DEFAULT }
  | "lambda" { FUN }
  | "let" { LET }
  | "par" { PAR }
  | "=>" { ARROW }
  | "=" { EQ }
  | "@" { AT }
  | "declare-datatypes" { DATA }
  | "assert" { ASSERT }
  | "assert-not" { ASSERT_NOT }
  | "declare-sort" { DECLARE_SORT }
  | "declare-fun" { DECLARE_FUN }
  | "declare-const" { DECLARE_CONST }
  | "define-fun" { DEFINE_FUN }
  | "define-fun-rec" { DEFINE_FUN_REC }
  | "define-funs-rec" { DEFINE_FUNS_REC }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "check-sat" { CHECK_SAT }
  | "result" { RESULT_RESULT }
  | "type" { RESULT_TYPE }
  | "val" { RESULT_VAL }
  | "SAT" { RESULT_SAT }
  | "UNSAT" { RESULT_UNSAT }
  | "UNKNOWN" { RESULT_UNKNOWN }
  | "TIMEOUT" { RESULT_TIMEOUT }
  | ":model" { RESULT_ATOM_MODEL }
  | ":reason" { RESULT_ATOM_REASON }
  | ident { IDENT(Lexing.lexeme lexbuf) }
  | quoted {
      (* TODO: unescape *)
      let s = Lexing.lexeme lexbuf in
      let s = String.sub s 1 (String.length s -2) in (* remove " " *)
      QUOTED s }
  | _ as c
    {
      let loc = Loc.of_lexbuf lexbuf in
      Parsing_utils.lex_error_ ~loc "unexpected char '%c'" c
    }

{

}
