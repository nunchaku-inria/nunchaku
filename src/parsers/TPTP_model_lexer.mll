
{
  open Nunchaku_core
  open TPTP_model_parser
}

let printable_char = [^ '\n']
let not_star_slash = ([^ '*']* '*'+ [^ '/' '*'])* [^ '*']*
let comment_line = ['%' '#'] printable_char*
let comment_block = '/' '*' not_star_slash '*' '/'
let comment = comment_line | comment_block

let sq_char = [^ '\\' '''] | "\\\\" | "\\'"
let do_char = [^ '"' '\\' ] |  "\\\\" | "\\\""
let single_quoted = ''' sq_char+ '''
let distinct_object = '"' do_char* '"'

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
let decimal_fraction = decimal dot_decimal
let decimal_exponent = (decimal | decimal_fraction) ['e' 'E'] integer
let unsigned_real = decimal_fraction | decimal_exponent
let signed_real = sign unsigned_real
let real = signed_real | unsigned_real
let unsigned_rational = decimal '/' positive_decimal
let signed_rational = sign unsigned_rational
let rational = signed_rational | unsigned_rational

let lower_alpha = ['a' - 'z']
let upper_alpha = ['A' - 'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let upper_word = upper_alpha alpha_numeric*
let lower_word = lower_alpha alpha_numeric*
let dollar_word = '$' lower_word

rule token = parse
  | comment_line { token lexbuf }
  | comment_block { token lexbuf }  (* TODO: count new lines in lexeme lexbuf *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | eof { EOI }
  | "fof" { FOF }
  | '|' { VLINE }
  | '&' { AND }
  | '!' { FORALL }
  | "$true" { TRUE }
  | "$false" { FALSE }
  | '~' { NOT }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | '[' { LEFT_BRACKET }
  | ']' { RIGHT_BRACKET }
  | '=' { EQUAL }
  | "<=>" { EQUIV }
  | ':' { COLON }
  | ',' { COMMA }
  | '.' { DOT }
  | "fi_domain" { ROLE_FI_DOMAIN }
  | "fi_functors" { ROLE_FI_FUNCTORS }
  | "fi_predicates" { ROLE_FI_PREDICATES }
  (*
  | "$let_tf" { LET_TF }
  | "$let_tf" { LET_FF }
  *)
  | lower_word { LOWER_WORD(Lexing.lexeme lexbuf) }
  | upper_word { UPPER_WORD(Lexing.lexeme lexbuf) }
  | dollar_word { DOLLAR_WORD(Lexing.lexeme lexbuf) }
  | single_quoted { SINGLE_QUOTED(Lexing.lexeme lexbuf) }
  | distinct_object { DISTINCT_OBJECT(Lexing.lexeme lexbuf) }
  | integer { INTEGER(Lexing.lexeme lexbuf) }
  | _ as c
    { let loc = Location.of_lexbuf lexbuf in
      Parsing_utils.lex_error_ ~loc "lexer fails on char %c" c }


{
  let parse_str_ p s = p token (Lexing.from_string s)

  let try_parse_ p s =
    try CCError.return (parse_str_ p s)
    with e -> CCError.fail (Printexc.to_string e)
}
