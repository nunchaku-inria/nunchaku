
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for TPTP models}
*)

%{

  open Nunchaku_core

  module L = Location
  module A = TPTP_model_ast

  (* remove quote from some symbols *)
  let remove_quotes s =
    assert (s.[0] = '\'' && s.[String.length s - 1] = '\'');
    String.sub s 1 (String.length s - 2)
%}

%token EOI

%token COLON
%token DOT
%token COMMA
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_BRACKET
%token RIGHT_BRACKET

%token NOT
%token AND
%token EQUAL
%token VLINE

%token TRUE
%token FALSE

%token FORALL

%token UNDERSCORE

%token ROLE_FI_DOMAIN
%token ROLE_FI_FUNCTORS
%token ROLE_FI_PREDICATES

%token FOF

%token <string> LOWER_WORD
%token <string> UPPER_WORD
%token <string> SINGLE_QUOTED
%token <string> DISTINCT_OBJECT
%token <string> DOLLAR_WORD
%token <string> INTEGER

%start <TPTP_model_ast.statement> parse_statement
%start <TPTP_model_ast.statement list> parse_statement_list

%%

parse_statement: s=statement EOI {s}
parse_statement_list: l=list(statement) EOI { l }


statement:
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_DOMAIN COMMA f=form RIGHT_PAREN DOT
    { let loc = L.mk_pos $startpos $endpos in A.mk_fi_domain name f }
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_FUNCTORS COMMA l=equations RIGHT_PAREN DOT
    { let loc = L.mk_pos $startpos $endpos in A.mk_fi_functors name l }
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_PREDICATES COMMA l=atoms RIGHT_PAREN DOT
    { let loc = L.mk_pos $startpos $endpos in A.mk_fi_predicates name l }
  | error
    { let loc = L.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected statement" }

form:
  | f=or_form { f }
  | FORALL LEFT_BRACKET v=var RIGHT_BRACKET COLON f=form
    { A.forall v f }

or_form:
  | l=and_form VLINE r=and_form { A.or_ l r }
  | f=and_form { f }

and_form:
  | f=unary_form { f }
  | l=unary_form AND r=and_form
    { A.and_ l r }

unary_form:
  | LEFT_PAREN f=form RIGHT_PAREN { f }
  | f=atomic_form { f }
  | NOT f=unary_form
    { A.not_ f }

atomic_form:
  | l=term EQUAL r=term
    { A.eq l r }
  | t=term
    { A.atom t }
  | TRUE { A.true_ }
  | FALSE { A.false_ }

atom:
  | f=atomic_form { f }
  | NOT f=atom { A.not_ f }

equation:
  | LEFT_PAREN e=equation RIGHT_PAREN { e }
  | l=term EQUAL r=term { l, r }
equations:
  | LEFT_PAREN l=equations RIGHT_PAREN { l }
  | l=separated_nonempty_list(AND, equation) { l }

atoms:
  | LEFT_PAREN l=atoms RIGHT_PAREN { l }
  | l=separated_nonempty_list(AND, atom) { l }

term:
  | v=var { A.var v }
  | f=DISTINCT_OBJECT { A.const f }
  | f=LOWER_WORD { A.const f }
  | f=LOWER_WORD LEFT_PAREN l=separated_nonempty_list(COMMA, term) RIGHT_PAREN
    { A.app f l }
  | LEFT_PAREN t=term RIGHT_PAREN { t }

var:
  | v=UPPER_WORD { v }

name:
  | w=LOWER_WORD { w }
  | w=SINGLE_QUOTED { remove_quotes w }
  | i=INTEGER { i }

%%


