{
  type token =
    | ATOM of string
    | LIST_OPEN
    | LIST_CLOSE
    | EOI

  exception Error of Location.t * string

  let remove_quotes s =
    assert (
      (s.[0] = '\'' && s.[String.length s - 1] = '\'') ||
      (s.[0] = '"' && s.[String.length s - 1] = '"'));
    String.sub s 1 (String.length s - 2)
}

let newline = '\n' | "\r\n"
let white = [' ' '\r' '\t'] | newline

let comment_line = ';' [^ '\n']*
let printable_char = [^ '\n']

let id = [^ ')' '(' ' ' '\t' '\r' '\n']+
let string = '"' ([^ '"'] | "\\\"")* '"'

rule token = parse
  | comment_line { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | white { token lexbuf }
  | eof { EOI }
  | '(' { LIST_OPEN }
  | ')' { LIST_CLOSE }
  | id { ATOM (Lexing.lexeme lexbuf) }
  | string { ATOM (remove_quotes (Lexing.lexeme lexbuf)) }
  | _ as c
    { let loc = Location.of_lexbuf lexbuf in
      raise (Error (loc, Printf.sprintf "lexing failed on char %c" c)) }

