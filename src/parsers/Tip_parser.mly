

(* This file is free software, part of tip-parser. See file "license" for more details. *)

(** {1 Parser for TIP} *)

(* vim:SyntasticToggleMode:
   vim:set ft=yacc: *)

%{
  open Nunchaku_core

%}

%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN

%token BOOL
%token PAR
%token ARROW

%token TRUE
%token FALSE
%token OR
%token AND
%token DISTINCT
%token NOT
%token EQ
%token IF
%token MATCH
%token CASE
%token DEFAULT
%token FUN
%token LET
%token AS
%token AT

%token DATA
%token ASSERT
%token ASSERT_NOT
%token FORALL
%token EXISTS
%token DECLARE_SORT
%token DECLARE_CONST
%token DECLARE_FUN
%token DEFINE_FUN
%token DEFINE_FUN_REC
%token DEFINE_FUNS_REC
%token CHECK_SAT

%token RESULT_RESULT
%token RESULT_SAT
%token RESULT_UNSAT
%token RESULT_TIMEOUT
%token RESULT_UNKNOWN
%token RESULT_VAL
%token RESULT_TYPE

%token RESULT_ATOM_MODEL
%token RESULT_ATOM_REASON

%token <string>IDENT
%token <string>QUOTED

%start <Tip_ast.term> parse_term
%start <Tip_ast.ty> parse_ty
%start <Tip_ast.statement> parse
%start <Tip_ast.statement list> parse_list
%start <Tip_ast.Smbc_res.t> parse_smbc_res

%%

parse_list: l=stmt* EOI {l}
parse: t=stmt EOI { t }
parse_term: t=term EOI { t }
parse_ty: t=ty EOI { t }
parse_smbc_res: r=smbc_res EOI { r }

cstor_arg:
  | LEFT_PAREN name=IDENT ty=ty RIGHT_PAREN { name, ty }

cstor:
  | LEFT_PAREN c=IDENT RIGHT_PAREN { Tip_ast.mk_cstor c [] }
  | LEFT_PAREN c=IDENT l=cstor_arg+ RIGHT_PAREN
    { Tip_ast.mk_cstor c l }

data:
  | LEFT_PAREN s=IDENT l=cstor+ RIGHT_PAREN { s,l }

fun_def_mono:
  | f=IDENT
    LEFT_PAREN args=typed_var* RIGHT_PAREN
    ret=ty
    { f, args, ret }

fun_decl_mono:
  | f=IDENT
    LEFT_PAREN args=ty* RIGHT_PAREN
    ret=ty
    { f, args, ret }

fun_decl:
  | tup=fun_decl_mono { let f, args, ret = tup in [], f, args, ret }
  | LEFT_PAREN
      PAR
      LEFT_PAREN tyvars=tyvar* RIGHT_PAREN
      LEFT_PAREN tup=fun_decl_mono RIGHT_PAREN
    RIGHT_PAREN
    { let f, args, ret = tup in tyvars, f, args, ret }

fun_rec:
  | tup=fun_def_mono body=term
    {
      let f, args, ret = tup in
      let loc = Location.mk_pos $startpos $endpos in 
      Tip_ast.mk_fun_rec ~loc ~ty_vars:[] f args ret body
    }
  | LEFT_PAREN
      PAR
      LEFT_PAREN l=tyvar* RIGHT_PAREN
      LEFT_PAREN tup=fun_def_mono body=term RIGHT_PAREN
    RIGHT_PAREN
    {
      let f, args, ret = tup in
      let loc = Location.mk_pos $startpos $endpos in 
      Tip_ast.mk_fun_rec ~loc ~ty_vars:l f args ret body
    }

funs_rec_decl:
  | LEFT_PAREN tup=fun_def_mono RIGHT_PAREN
    {
      let f, args, ret = tup in
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.mk_fun_decl ~loc ~ty_vars:[] f args ret
    }
  | LEFT_PAREN
      PAR
      LEFT_PAREN l=tyvar* RIGHT_PAREN
      LEFT_PAREN tup=fun_def_mono RIGHT_PAREN
    RIGHT_PAREN
    {
      let f, args, ret = tup in
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.mk_fun_decl ~loc ~ty_vars:l f args ret
    }

assert_not:
  | LEFT_PAREN
      PAR LEFT_PAREN tyvars=tyvar+ RIGHT_PAREN t=term
    RIGHT_PAREN
  { tyvars, t }
  | t=term
  { [], t }

stmt:
  | LEFT_PAREN ASSERT t=term RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.assert_ ~loc t
    }
  | LEFT_PAREN DECLARE_SORT s=IDENT n=IDENT RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      try
        let n = int_of_string n in
        Tip_ast.decl_sort ~loc s ~arity:n
      with Failure _ ->
        Tip_ast.parse_errorf ~loc "expected arity to be an integer, not `%s`" n
    }
  | LEFT_PAREN DATA
      LEFT_PAREN vars=tyvar* RIGHT_PAREN
      LEFT_PAREN l=data+ RIGHT_PAREN
    RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.data ~loc vars l
    }
  | LEFT_PAREN DECLARE_FUN tup=fun_decl RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      let ty_vars, f, args, ret = tup in
      Tip_ast.decl_fun ~loc ~ty_vars f args ret
    }
  | LEFT_PAREN DECLARE_CONST f=IDENT ty=ty RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.decl_fun ~loc ~ty_vars:[] f [] ty
    }
  | LEFT_PAREN DEFINE_FUN f=fun_rec RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.fun_rec ~loc f
    }
  | LEFT_PAREN
    DEFINE_FUN_REC
    f=fun_rec
    RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.fun_rec ~loc f
    }
  | LEFT_PAREN
    DEFINE_FUNS_REC
      LEFT_PAREN decls=funs_rec_decl+ RIGHT_PAREN
      LEFT_PAREN bodies=term+ RIGHT_PAREN
    RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.funs_rec ~loc decls bodies
    }
  | LEFT_PAREN
    ASSERT_NOT
    tup=assert_not
    RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      let ty_vars, f = tup in
      Tip_ast.assert_not ~loc ~ty_vars f
    }
  | LEFT_PAREN CHECK_SAT RIGHT_PAREN
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.check_sat ~loc ()
    }
  | error
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.parse_errorf ~loc "expected statement"
    }

var:
  | s=IDENT { s }
tyvar:
  | s=IDENT { s }

ty:
  | BOOL { let loc = Location.mk_pos $startpos $endpos in Tip_ast.ty_bool ~loc }
  | s=IDENT { let loc = Location.mk_pos $startpos $endpos in Tip_ast.ty_const ~loc s }
  | LEFT_PAREN s=IDENT args=ty+ RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.ty_app ~loc s args }
  | LEFT_PAREN ARROW tup=ty_arrow_args RIGHT_PAREN
    {
      let args, ret = tup in
      let loc = Location.mk_pos $startpos $endpos in Tip_ast.ty_arrow_l ~loc args ret }

ty_arrow_args:
  | a=ty ret=ty { [a], ret }
  | a=ty tup=ty_arrow_args { a :: fst tup, snd tup }

typed_var:
  | LEFT_PAREN s=IDENT ty=ty RIGHT_PAREN { s, ty }

case:
  | LEFT_PAREN
      CASE
      c=IDENT
      rhs=term
    RIGHT_PAREN
    { Tip_ast.Match_case (c, [], rhs) }
  | LEFT_PAREN
      CASE
      LEFT_PAREN c=IDENT vars=var+ RIGHT_PAREN
      rhs=term
    RIGHT_PAREN
    { Tip_ast.Match_case (c, vars, rhs) }
  | LEFT_PAREN
     CASE DEFAULT rhs=term
    RIGHT_PAREN
    { Tip_ast.Match_default rhs }

binding:
  | LEFT_PAREN v=var t=term RIGHT_PAREN { v, t }

term:
  | TRUE { let loc = Location.mk_pos $startpos $endpos in Tip_ast.true_ ~loc }
  | FALSE { let loc = Location.mk_pos $startpos $endpos in Tip_ast.false_ ~loc }
  | s=QUOTED { let loc = Location.mk_pos $startpos $endpos in Tip_ast.const ~loc s }
  | s=IDENT { let loc = Location.mk_pos $startpos $endpos in Tip_ast.const ~loc s }
  | LEFT_PAREN t=term RIGHT_PAREN { t }
  | LEFT_PAREN IF a=term b=term c=term RIGHT_PAREN {
    let loc = Location.mk_pos $startpos $endpos in Tip_ast.if_ ~loc a b c }
  | LEFT_PAREN OR l=term+ RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.or_ ~loc l }
  | LEFT_PAREN AND l=term+ RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.and_ ~loc l }
  | LEFT_PAREN NOT t=term RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.not_ ~loc t }
  | LEFT_PAREN DISTINCT l=term+ RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.distinct ~loc l }
  | LEFT_PAREN EQ a=term b=term RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.eq ~loc a b }
  | LEFT_PAREN ARROW a=term b=term RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.imply ~loc a b }
  | LEFT_PAREN f=IDENT args=term+ RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.app ~loc f args }
  | LEFT_PAREN AT f=term t=term RIGHT_PAREN { let loc = Location.mk_pos $startpos $endpos in Tip_ast.ho_app ~loc f t }
  | LEFT_PAREN
      MATCH
      lhs=term
      l=case+
    RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.match_ ~loc lhs l }
  | LEFT_PAREN
      FUN
      LEFT_PAREN vars=typed_var+ RIGHT_PAREN
      body=term
    RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.fun_l ~loc vars body }
  | LEFT_PAREN
      LET
      LEFT_PAREN l=binding+ RIGHT_PAREN
      r=term
    RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.let_ ~loc l r }
  | LEFT_PAREN AS t=term ty=ty RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.cast ~loc t ~ty }
  | LEFT_PAREN FORALL LEFT_PAREN vars=typed_var+ RIGHT_PAREN
    f=term
    RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.forall ~loc vars f }
  | LEFT_PAREN EXISTS LEFT_PAREN vars=typed_var+ RIGHT_PAREN
    f=term
    RIGHT_PAREN
    { let loc = Location.mk_pos $startpos $endpos in Tip_ast.exists ~loc vars f }
  | error
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.parse_errorf ~loc "expected term"
    }

smbc_model:
  | LEFT_PAREN e=smbc_model_entry* RIGHT_PAREN { e }
  | error
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.parse_errorf ~loc "expected SMBC model (a list of entries)"
    }

smbc_model_entry:
  | LEFT_PAREN RESULT_VAL a=term b=term RIGHT_PAREN { Tip_ast.Smbc_res.Val (a,b) }
  | LEFT_PAREN
      RESULT_TYPE a=ty LEFT_PAREN dom=var* RIGHT_PAREN
    RIGHT_PAREN
    { Tip_ast.Smbc_res.Ty (a,dom) }
  | error
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.parse_errorf ~loc
        "expected SMBC model entry: (val term term) or (type ty domain)"
    }

smbc_unknown_reason:
  | { "" }
  | RESULT_ATOM_REASON s=IDENT { s }
  | RESULT_ATOM_REASON s=QUOTED { s }

smbc_res:
  | LEFT_PAREN RESULT_RESULT RESULT_UNSAT RIGHT_PAREN { Tip_ast.Smbc_res.Unsat }
  | LEFT_PAREN RESULT_RESULT? RESULT_TIMEOUT RIGHT_PAREN { Tip_ast.Smbc_res.Timeout }
  | LEFT_PAREN RESULT_RESULT RESULT_SAT RESULT_ATOM_MODEL? m=smbc_model RIGHT_PAREN { Tip_ast.Smbc_res.Sat m }
  | LEFT_PAREN RESULT_RESULT RESULT_UNKNOWN r=smbc_unknown_reason RIGHT_PAREN { Tip_ast.Smbc_res.Unknown r }
  | error
    {
      let loc = Location.mk_pos $startpos $endpos in
      Tip_ast.parse_errorf ~loc "expected SMBC result"
    }

%%
