{
  type token =
    | ATOM of string
    | LIST_OPEN
    | LIST_CLOSE
    | EOI

  exception Error of Location.t * string

  let error lexbuf msg =
    let loc = Location.of_lexbuf lexbuf in
    raise (Error (loc,msg))

  type unescape_state =
    | Not_escaped
    | Escaped
    | Escaped_int_1 of int
    | Escaped_int_2 of int

  let char_equal (a : char) b = Stdlib.(=) a b

  let count_newlines lexbuf s : unit =
    let i = ref 0 in
    try
      while !i < String.length s do
        i := 1 + String.index_from s !i '\n';
        Lexing.new_line lexbuf;
      done;
    with Not_found -> ()
}

let newline = '\n' | "\r\n"
let white = [' ' '\r' '\t'] | newline

let comment_line = ';' [^ '\n']*
let printable_char = [^ '\n']

let num = ['0'-'9']
let letter = (['a'-'z'] | ['A'-'Z'])
let simple_symbol =
  (num | letter | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/')+

let invbars = '|' ([^ '\\' '|' '\n'] | '\\' '|')+ '|'

rule token = parse
  | comment_line { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | white { token lexbuf }
  | eof { EOI }
  | '(' { LIST_OPEN }
  | ')' { LIST_CLOSE }
  | simple_symbol { ATOM (Lexing.lexeme lexbuf) }
  | invbars {
      let s = Lexing.lexeme lexbuf in
      count_newlines lexbuf s;
      ATOM(s)
    }
  | _ as c
    { let loc = Location.of_lexbuf lexbuf in
      raise (Error (loc, Printf.sprintf "lexing failed on char %c" c)) }

