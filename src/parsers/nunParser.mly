
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{

  module L = NunLocation
  module A = NunUntypedAST
  module Sym = NunSymbol

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
%token AND

%token LOGIC_TRUE
%token LOGIC_FALSE
%token LOGIC_AND
%token LOGIC_OR
%token LOGIC_NOT
%token LOGIC_IMPLY
%token LOGIC_EQUIV
%token LOGIC_FORALL
%token LOGIC_EXISTS
%token PROP
%token TYPE

%token AXIOM
%token DEF
%token DECL

%token ARROW
%token FUN

%token <string> LOWER_WORD
%token <string> UPPER_WORD

%start <NunUntypedAST.statement> parse_statement
%start <NunUntypedAST.statement list> parse_statement_list
%start <NunUntypedAST.term> parse_term
%start <NunUntypedAST.ty> parse_ty

%%

parse_statement: s=statement EOI {s}
parse_term: t=term EOI {t}
parse_ty: t=ty EOI {t}
parse_statement_list: l=list(statement) EOI { l }

ty_var:
  | WILDCARD
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_wildcard ~loc ()
    }
  | name=LOWER_WORD
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_var ~loc name
    }

atomic_ty:
  | v=ty_var { v }
  | TYPE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_sym ~loc Sym.type_
    }
  | LEFT_PAREN t=ty RIGHT_PAREN { t }

/* application */
app_ty:
  | t=atomic_ty { t }
  | t=atomic_ty u=atomic_ty+
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_app ~loc t u
    }

ty:
  | t=app_ty {t}
  | t=app_ty ARROW u=ty
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_arrow ~loc t u
    }
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

/* variable without a location */
raw_var: w=LOWER_WORD { w }

typed_var:
  | v=raw_var { v, None }
  | v=raw_var COLUMN t=atomic_ty { v, Some t }

var:
  | name=raw_var
    {
      let loc = L.mk_pos $startpos $endpos in
      A.var ~loc name
    }

atomic_term:
  | v=var { v }
  | PROP
    {
      let loc = L.mk_pos $startpos $endpos in
      A.sym ~loc Sym.prop
    }
  | LOGIC_TRUE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.sym ~loc Sym.true_
    }
  | LOGIC_FALSE
    {
      let loc = L.mk_pos $startpos $endpos in
      A.sym ~loc Sym.false_
    }
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
      A.app ~loc (A.sym ~loc Sym.not_) [t]
    }

and_term:
  | t=apply_term { t }
  | t=apply_term LOGIC_AND u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.sym ~loc Sym.and_) [t; u]
    }

or_term:
  | t=and_term { t }
  | t=and_term LOGIC_OR u=or_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.sym ~loc Sym.or_) [t; u]
    }
  | t=and_term LOGIC_IMPLY u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.sym ~loc Sym.imply) [t; u]
    }
  | t=and_term LOGIC_EQUIV u=and_term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc (A.sym ~loc Sym.equiv) [t; u]
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
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

statement:
  | DECL v=raw_var COLUMN t=ty DOT
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
  | error
    {
      let loc = L.mk_pos $startpos $endpos in
      raise (A.ParseError loc)
    }

%%
