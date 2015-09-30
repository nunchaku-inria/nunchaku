
(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Input AST} *)

module Loc = NunLocation

type var = string

type ty = ty_node Loc.with_loc
and ty_node =
  | TyVar of var
  | TyApp of ty * ty list
  | TyArrow of ty * ty

type term = term_node Loc.with_loc
and term_node =
  | Var of var
  | App of term * term list
  | Fun of var * term

type statement_node =
  | Decl of var * ty (* type declaration *)
  | Def of var * term (* definition *)
  | Axiom of term (* axiom *)

type statement = statement_node Loc.with_loc

let ty_var ?loc v = Loc.with_loc ?loc (TyVar v)
let ty_app ?loc a l = Loc.with_loc ?loc (TyApp (a,l))
let ty_arrow ?loc a b = Loc.with_loc ?loc (TyArrow (a,b))

let var ?loc v = Loc.with_loc ?loc (Var v)

let app ?loc t l = Loc.with_loc ?loc (App (t,l))
let fun_ ?loc v t = Loc.with_loc ?loc (Fun(v,t))
let fun_l ?loc vars t = List.fold_right (fun v t -> fun_ ?loc v t) vars t

let decl ?loc v t = Loc.with_loc ?loc (Decl(v,t))
let def ?loc v t = Loc.with_loc ?loc (Def (v,t))
let axiom ?loc t = Loc.with_loc ?loc (Axiom t)


