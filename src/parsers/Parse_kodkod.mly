
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Kodkod models}
*)

%{
  open Nunchaku_core
%}

%token<Ast_kodkod.section> SECTION
%token RELATION
%token COLON (* : *)
%token COMMA (* , *)
%token L_BRACE
%token R_BRACE
%token L_BRACKET
%token R_BRACKET
%token<string> IDENT (* s0 *)
%token EQUAL (* = *)
%token<int> ATOM (* A57 *)

%start<Ast_kodkod.model> parse_model

%%

parse_model:
  | L_BRACE l=separated_nonempty_list(COMMA, model_elem) R_BRACE { l }

model_elem:
  | i=IDENT EQUAL l=lla
    { Ast_kodkod.make_rel i l }

lla:
  | L_BRACKET l=separated_list(COMMA,la) R_BRACKET { l }

la:
  | L_BRACKET l=separated_list(COMMA, ATOM) R_BRACKET { l }

%%
