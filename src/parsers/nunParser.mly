
(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{

  module L = NunLocation
  module A = NunAST

%}


%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN

%token WILDCARD
%token DOT
%token COLUMN
%token EQDEF

%token ARROW

%token DOUBLEARROW
%token FUN

%token AXIOM
%token DEF
%token DECL

%token <string> LOWER_WORD
%token <string> UPPER_WORD

%start <NunAST.statement> parse_statement
%start <NunAST.statement list> parse_statement_list
%start <NunAST.term> parse_term
%start <NunAST.ty> parse_ty

%%

parse_statement: s=statement EOI {s}
parse_term: t=term EOI {t}
parse_ty: t=ty EOI {t}
parse_statement_list: l=list(statement) EOI { l }

ty_var:
  | WILDCARD
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_var ~loc "_"
    }
  | name=LOWER_WORD
    {
      let loc = L.mk_pos $startpos $endpos in
      A.ty_var ~loc name
    }

atomic_ty:
  | v=ty_var { v }
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

var:
  | name=raw_var
    {
      let loc = L.mk_pos $startpos $endpos in
      A.var ~loc name
    }

atomic_term:
  | v=var { v }
  | LEFT_PAREN t=term RIGHT_PAREN { t }

term:
  | t=atomic_term { t }
  | t=atomic_term u=atomic_term+
    {
      let loc = L.mk_pos $startpos $endpos in
      A.app ~loc t u
    }
  | FUN vars=list(raw_var) DOUBLEARROW t=term
    {
      let loc = L.mk_pos $startpos $endpos in
      A.fun_l ~loc vars t
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
  | DEF v=raw_var l=raw_var* EQDEF t=term DOT
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
