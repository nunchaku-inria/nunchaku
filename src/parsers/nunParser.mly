
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
%token LET
%token IN
%token IF
%token THEN
%token ELSE
%token AND
%token AT

%token LOGIC_TRUE
%token LOGIC_FALSE
%token LOGIC_AND
%token LOGIC_OR
%token LOGIC_NOT
%token LOGIC_IMPLY
%token LOGIC_EQUIV
%token LOGIC_FORALL
%token LOGIC_EXISTS
%token LOGIC_EQ

%token PROP
%token TYPE

%token AXIOM
%token DEF
%token DECL
%token GOAL

%token ARROW
%token FUN
%token FORALL

%token <string> LOWER_WORD
%token <string> UPPER_WORD

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

and_term:
  | t=apply_term { t }
  | t=apply_term LOGIC_EQ u=apply_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Eq) [t; u]
    }
  | t=apply_term LOGIC_AND u=and_term
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
  | t=and_term LOGIC_EQUIV u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.builtin ~loc B.Equiv) [t; u]
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
  | FORALL vars=typed_ty_var+ DOT t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_forall_list ~loc vars t
    }
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

statement:
  | DECL v=raw_var COLUMN t=term DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.decl ~loc v t
    }
  | DEF v=typed_var l=typed_var* EQDEF t=term DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.def_l ~loc v l t
    }
  | AXIOM t=term DOT
    {
      let loc = L.mk_pos $startpos $endpos in
      A.axiom ~loc t
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
