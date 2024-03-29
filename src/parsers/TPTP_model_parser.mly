
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for TPTP models}
*)

%{

  open Nunchaku_core

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

/* %token UNDERSCORE */

%token ROLE_FI_DOMAIN
%token ROLE_FI_FUNCTORS
%token ROLE_FI_PREDICATES

%token FOF

%token <string> LOWER_WORD
%token <string> UPPER_WORD
%token <string> SINGLE_QUOTED
%token <string> DISTINCT_OBJECT
/* %token <string> DOLLAR_WORD */
%token <string> INTEGER

%start <TPTP_model_ast.statement> parse_statement
%start <TPTP_model_ast.statement list> parse_statement_list

%%

parse_statement: s=statement EOI {s}
parse_statement_list: l=list(statement) EOI { l }

statement:
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_DOMAIN COMMA f=form RIGHT_PAREN DOT
    { TPTP_model_ast.mk_fi_domain name f }
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_FUNCTORS
    COMMA f=form RIGHT_PAREN DOT
    { let loc = Location.mk_pos $startpos $endpos in
      let vars, f = TPTP_model_ast.open_forall f in
      TPTP_model_ast.mk_fi_functors ~loc name vars (TPTP_model_ast.as_and_ ~loc f) }
  | FOF LEFT_PAREN name=name COMMA ROLE_FI_PREDICATES
    COMMA f=form RIGHT_PAREN DOT
    { let loc = Location.mk_pos $startpos $endpos in
      let vars, f = TPTP_model_ast.open_forall f in
      TPTP_model_ast.mk_fi_predicates ~loc name vars (TPTP_model_ast.as_and_ ~loc f) }
  | error
    { let loc = Location.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected statement" }

form:
  | f=or_form { f }

or_form:
  | l=and_form VLINE r=or_form { TPTP_model_ast.or_ l r }
  | f=and_form { f }

and_form:
  | f=unary_form { f }
  | l=unary_form AND r=and_form
    { TPTP_model_ast.and_ l r }

%inline forall_vars:
  | FORALL LEFT_BRACKET l=separated_nonempty_list(COMMA,var) RIGHT_BRACKET COLON { l }

unary_form:
  | vars=forall_vars f=atomic_form
    { TPTP_model_ast.forall_l vars f }
  | f=atomic_form { f }
  | NOT f=unary_form
    { TPTP_model_ast.not_ f }

atomic_form:
  | LEFT_PAREN f=form RIGHT_PAREN { f }
  | l=term EQUAL r=term
    { TPTP_model_ast.eq l r }
  | t=term
    { TPTP_model_ast.atom t }
  | t=term EQUIV TRUE
    { TPTP_model_ast.atom t }
  | t=term EQUIV FALSE
    { TPTP_model_ast.not_ (TPTP_model_ast.atom t) }
  | t=term EQUIV u=term
    { TPTP_model_ast.equiv t u }
  | TRUE { TPTP_model_ast.true_ }
  | FALSE { TPTP_model_ast.false_ }
  | error
    { let loc = Location.mk_pos $startpos $endpos in
      Parsing_utils.parse_error_ ~loc "expected atomic form" }

term:
  | v=var { TPTP_model_ast.var v }
  | f=DISTINCT_OBJECT { TPTP_model_ast.const f }
  | f=LOWER_WORD { TPTP_model_ast.const f }
  | f=LOWER_WORD LEFT_PAREN l=separated_nonempty_list(COMMA, term) RIGHT_PAREN
    { TPTP_model_ast.app f l }

var:
  | v=UPPER_WORD { v }

name:
  | w=LOWER_WORD { w }
  | w=SINGLE_QUOTED { remove_quotes w }
  | i=INTEGER { i }

%%


