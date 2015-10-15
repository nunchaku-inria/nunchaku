
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{

  module L = NunLocation
  module A = NunUntypedAST
  module B = A.Builtin

%}


%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN

%token WILDCARD
%token DOT
%token COLUMN
%token EQDEF
%token AS
%token LET
%token IN
%token IF
%token THEN
%token ELSE
%token AND
%token AT
%token META_VAR

%token LOGIC_TRUE
%token LOGIC_FALSE
%token LOGIC_AND
%token LOGIC_OR
%token LOGIC_NOT
%token LOGIC_IMPLY
%token LOGIC_FORALL
%token LOGIC_EXISTS
%token LOGIC_EQ

%token PROP
%token TYPE

%token SEMI_COLUMN
%token AXIOM
%token REC
%token SPEC
%token DATA
%token CODATA
%token VAL
%token GOAL

%token ARROW
%token FUN
%token PI
%token VERTICAL_BAR

%token <string> LOWER_WORD

%start <NunUntypedAST.statement> parse_statement
%start <NunUntypedAST.statement list> parse_statement_list
%start <NunUntypedAST.term> parse_term
%start <NunUntypedAST.ty> parse_ty

%%

parse_statement: s=statement EOI {s}
parse_term: t=term EOI {t}
parse_ty: t=term EOI {t}
parse_statement_list: l=list(statement) EOI { l }

/* variable without a location */
raw_var: w=LOWER_WORD { w }

typed_var:
  | v=raw_var { v, None }
  | LEFT_PAREN v=raw_var COLUMN t=term RIGHT_PAREN { v, Some t }

typed_ty_var:
  | v=raw_var { v }
  | v=raw_var COLUMN TYPE { v }
  | LEFT_PAREN v=raw_var COLUMN TYPE RIGHT_PAREN { v }

var:
  | WILDCARD
    {
      let loc = L.mk_pos $startpos $endpos in
      A.wildcard ~loc ()
    }
  | name=raw_var
    {
      let loc = L.mk_pos $startpos $endpos in
      A.var ~loc name
    }

at_var:
  | AT v=raw_var
    {
      let loc = L.mk_pos $startpos $endpos in
      A.at_var ~loc v
    }

meta_var:
  | META_VAR v=raw_var
    {
      let loc = L.mk_pos $startpos $endpos in
      A.meta_var ~loc v
    }

const:
  | TYPE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.builtin ~loc B.Type
    }
  | PROP
    {
      let loc = L.mk_pos $startpos $endpos in
      A.builtin ~loc B.Prop
    }
  | LOGIC_TRUE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.builtin ~loc B.True
    }
  | LOGIC_FALSE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.builtin ~loc B.False
    }

atomic_term:
  | v=var { v }
  | v=at_var { v }
  | v=meta_var { v }
  | t=const { t }
  | LEFT_PAREN t=term RIGHT_PAREN { t }

apply_term:
  | t=atomic_term { t }
  | t=atomic_term u=atomic_term+
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc t u
    }
  | LOGIC_NOT t=atomic_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Not) [t]
    }

eq_term:
  | t=apply_term { t }
  | t=apply_term LOGIC_EQ u=apply_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Eq) [t; u]
    }

and_term:
  | t=eq_term { t }
  | t=eq_term LOGIC_AND u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.And) [t; u]
    }

or_term:
  | t=and_term { t }
  | t=and_term LOGIC_OR u=or_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Or) [t; u]
    }
  | t=and_term LOGIC_IMPLY u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Imply) [t; u]
    }

term:
  | t=or_term { t }
  | FUN vars=typed_var+ DOT t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.fun_l ~loc vars t
    }
  | LET v=raw_var EQDEF t=term IN u=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.let_ ~loc v t u
    }
  | IF a=term THEN b=term ELSE c=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ite ~loc a b c
    }
  | LOGIC_FORALL vars=typed_var+ DOT t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.forall_list ~loc vars t
    }
  | LOGIC_EXISTS vars=typed_var+ DOT t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.exists_list ~loc vars t
    }
  | t=apply_term ARROW u=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_arrow ~loc t u
    }
  | PI vars=typed_ty_var+ DOT t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_forall_list ~loc vars t
    }
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

case:
  | v=raw_var EQDEF l=separated_nonempty_list(SEMI_COLUMN,term)
    {
      let loc = L.mk_pos $startpos $endpos in
      A.var ~loc v, v, l
    }
  | t=term AS v=raw_var EQDEF l=separated_nonempty_list(SEMI_COLUMN, term)
    { t, v, l }

mutual_cases:
  | l=separated_nonempty_list(AND, case) { l }

constructor:
  | v=raw_var COLUMN ty=term { v, ty }

constructors:
  | VERTICAL_BAR? l=separated_nonempty_list(VERTICAL_BAR, constructor) { l }

type_def:
  | t=raw_var EQDEF l=constructors  { t, A.builtin A.Builtin.Type, l }
  | t=raw_var COLUMN ty=term EQDEF l=constructors { t, ty, l }

mutual_types:
  | l=separated_nonempty_list(AND, type_def) { l }

statement:
  | VAL v=raw_var COLUMN t=term DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.decl ~loc v t
    }
  | AXIOM l=separated_nonempty_list(SEMI_COLUMN, term) DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.axiom ~loc l
    }
  | SPEC l=mutual_cases DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.spec ~loc l
    }
  | REC l=mutual_cases DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.rec_ ~loc l
    }
  | DATA l=mutual_types DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.data ~loc l
    }
  | CODATA l=mutual_types DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.codata ~loc l
    }
  | GOAL t=term DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.goal ~loc t
    }
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

%%
