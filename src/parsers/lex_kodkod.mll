{
open Nunchaku_core
open Parse_kodkod

module A = Ast_kodkod
}

let ident = ['a' - 'z'] ['a' - 'z' '_' '0' - '9']*
let atom = 'A' ['0' - '9']+

rule token = parse
| [' ' '\t' '\r'] { token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| "---OUTCOME---" { SECTION A.S_outcome }
| "---INSTANCE---" { SECTION A.S_instance }
| "---STATS---" { SECTION A.S_stats }
| "{" { L_BRACE }
| "}" { R_BRACE }
| "[" { L_BRACKET }
| "]" { R_BRACKET }
| ":" { COLON }
| "=" { EQUAL }
| "," { COMMA }
| ident { IDENT (Lexing.lexeme lexbuf) }
| atom {
  let s = Lexing.lexeme lexbuf in
  ATOM (int_of_string (String.sub s 1 (String.length s - 1))) }
| _ as c
  { let loc = Location.of_lexbuf lexbuf in
    Parsing_utils.lex_error_ ~loc "lexer `token` fails on char %c" c }

and result = parse
  | [' ' '\t' '\r'] { result lexbuf }
  | '\n' { Lexing.new_line lexbuf; result lexbuf }
  | "UNSATISFIABLE" { A.Unsat }
  | "SATISFIABLE" { A.Sat }
  | _ as c
    { let loc = Location.of_lexbuf lexbuf in
      Parsing_utils.lex_error_ ~loc "lexer `result` fails on char %c" c }

{
}
