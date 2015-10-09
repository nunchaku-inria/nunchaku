
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer for Nunchaku} *)

{

  exception LexError of string

  open NunParser

}

let printable_char = [^ '\n']
let comment_line = '#' printable_char*

let numeric = ['0' - '9']
let lower_alpha = ['a' - 'z']
let upper_alpha = ['A' - 'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let upper_word = upper_alpha alpha_numeric*
let lower_word = lower_alpha alpha_numeric*

let zero_numeric = '0'
let non_zero_numeric = ['1' - '9']
let numeric = ['0' - '9']
let sign = ['+' '-']

let dot_decimal = '.' numeric +
let positive_decimal = non_zero_numeric numeric*
let decimal = zero_numeric | positive_decimal
let unsigned_integer = decimal
let signed_integer = sign unsigned_integer
let integer = signed_integer | unsigned_integer

rule token = parse
  | eof { EOI }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | comment_line { token lexbuf }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | '.' { DOT }
  | '_' { WILDCARD }
  | ':' { COLUMN }
  | ';' { SEMI_COLUMN }
  | "=" { LOGIC_EQ }
  | ":=" { EQDEF }
  | "->" { ARROW }
  | "fun" { FUN }
  | "rec" { REC }
  | "spec" { SPEC }
  | "val" { VAL }
  | "type" { TYPE }
  | "prop" { PROP }
  | "axiom" { AXIOM }
  | "goal" { GOAL }
  | "let" { LET }
  | "in" { IN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "and" { AND }
  | "true" { LOGIC_TRUE }
  | "false" { LOGIC_FALSE }
  | "pi" { PI }
  | '&' { LOGIC_AND }
  | '|' { LOGIC_OR }
  | '~' { LOGIC_NOT }
  | '!' { LOGIC_FORALL }
  | '?' { LOGIC_EXISTS }
  | "=>" { LOGIC_IMPLY }
  | '@' { AT }
  | lower_word { LOWER_WORD(Lexing.lexeme lexbuf) }
  | upper_word { UPPER_WORD(Lexing.lexeme lexbuf) }
  | _ as c { raise (LexError (Printf.sprintf "lexer fails on char '%c'" c)) }

{
  module E = CCError
  module A = NunUntypedAST
  module Loc = NunLocation

  type 'a or_error = [`Ok of 'a | `Error of string ]

  type statement = A.statement
  type term = A.term
  type ty = A.ty

  let () = Printexc.register_printer
    (function
      | LexError msg -> Some ("lexing error: " ^ msg )
      | _ -> None
    )

  let parse_file file =
    try
      CCIO.with_in file
        (fun ic ->
          let lexbuf = Lexing.from_channel ic in
          Loc.set_file lexbuf file; (* for error reporting *)
          E.return (NunParser.parse_statement_list token lexbuf)
        )
    with e ->
      E.fail (Printexc.to_string e)

  let parse_stdin () =
    try
      let lexbuf = Lexing.from_channel stdin in
      Loc.set_file lexbuf "<stdin>"; (* for error reporting *)
      E.return (NunParser.parse_statement_list token lexbuf)
    with e ->
      E.fail (Printexc.to_string e)

  let parse_str_ p s = p token (Lexing.from_string s)

  let try_parse_ p s =
    try E.return (parse_str_ p s)
    with e -> E.fail (Printexc.to_string e)

  let ty_of_string = try_parse_ NunParser.parse_ty
  let ty_of_string_exn = parse_str_ NunParser.parse_ty

  let term_of_string = try_parse_ NunParser.parse_term
  let term_of_string_exn = parse_str_ NunParser.parse_term

  let statement_of_string = try_parse_ NunParser.parse_statement
  let statement_of_string_exn = parse_str_ NunParser.parse_statement
}
