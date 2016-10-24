
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for TPTP models}
*)

%{

  open Nunchaku

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
%token EQUIV
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
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_FUNCTORS
    COMMA l=equations RIGHT_PAREN DOT
    { let vars, l = l in
      A.mk_fi_functors name vars l }
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_PREDICATES
    COMMA l=atoms RIGHT_PAREN DOT
    { let vars, l = l in
      A.mk_fi_predicates name vars l }
  | error
    { let loc = L.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected statement" }

form:
  | f=or_form { f }
  | FORALL LEFT_BRACKET v=var RIGHT_BRACKET COLON f=form
    { A.forall v f }
  | error
    { let loc = L.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected form" }

or_form:
  | l=and_form VLINE r=or_form { A.or_ l r }
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
  | t=term EQUIV TRUE
    { A.atom t }
  | t=term EQUIV FALSE
    { A.not_ (A.atom t) }
  | t=term EQUIV u=term
    { A.equiv t u }
  | TRUE { A.true_ }
  | FALSE { A.false_ }
  | error
    { let loc = L.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected atomic form" }

atom:
  | f=atomic_form { f }
  | LEFT_PAREN f=atom RIGHT_PAREN { f }
  | NOT f=atom { A.not_ f }
  | FORALL LEFT_BRACKET v=var RIGHT_BRACKET COLON f=atom
    { A.forall v f }

%inline forall_vars:
  | FORALL LEFT_BRACKET l=separated_nonempty_list(COMMA,var) RIGHT_BRACKET COLON { l }

equation:
  | FORALL LEFT_BRACKET v=var RIGHT_BRACKET COLON e=equation
    { A.forall v e }
  | LEFT_PAREN e=equation RIGHT_PAREN { e }
  | l=term EQUAL r=term { A.eq l r }

equations:
  | LEFT_PAREN l=equations RIGHT_PAREN { l }
  | vars=forall_vars l=equations
    { let vars', l = l in vars @ vars', l }
  | l=separated_nonempty_list(AND, equation) { [], l }

atoms:
  | LEFT_PAREN l=atoms RIGHT_PAREN { l }
  | vars=forall_vars l=atoms
    { let vars', l = l in vars @ vars', l }
  | l=separated_nonempty_list(AND, atom) { [], l }
  | error
    { let loc = L.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected atom" }

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


