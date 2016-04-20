
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Relational FO Logic}

    This corresponds, roughly, to Kodkod's logic *)

(** {2 Types} *)

type tuple = ID.t list

type unop =
  | Flip (** flip p x y <=> p y x *)
  | Trans (** trans p == transitive closure *)

type binop =
  | Union
  | Inter
  | Diff
  | Join (** join (x,y) (y,z) == (x,z) *)
  | Concat (** concat (x1,y1) (x2,y2) == (x1,y1,x2,y2) *)

type mult =
  | M_no
  | M_one
  | M_some

type expr =
  | Const of ID.t
  | Var of expr Var.t
  | Unop of unop * expr
  | Binop of binop * expr * expr
  | Comprehension of expr Var.t * form

and form =
  | In of expr * expr
  | Mult of mult * expr
  | Not of form
  | And of form * form
  | Or of form * form
  | Forall of expr Var.t * form
  | Exists of expr Var.t * form

type decl = {
  decl_id: ID.t;
  decl_arity: int;
  decl_low: tuple list; (* lower bound *)
  decl_high: tuple list; (* higher bound *)
}

type problem = {
  pb_univ: ID.Set.t;
  pb_decls: decl CCVector.ro_vector;
  pb_goal: form;
  pb_meta: ProblemMetadata.t;
}

(** {2 Helpers} *)

val unop : unop -> expr -> expr
val binop : binop -> expr -> expr -> expr
val mult : mult -> expr -> form

val flip : expr -> expr
val trans : expr -> expr
val const : ID.t -> expr
val var : expr Var.t -> expr
val union : expr -> expr -> expr
val inter : expr -> expr -> expr
val diff : expr -> expr -> expr
val join : expr -> expr -> expr
val concat : expr -> expr -> expr
val comprehension : expr Var.t -> form -> expr

val in_ : expr -> expr -> form
val no : expr -> form (** expr has no tuples *)
val one : expr -> form (** expr has exactly one tuple *)
val some : expr -> form (** expr has at least one tuple *)
val not_ : form -> form
val and_ : form -> form -> form
val and_l : form list -> form
val or_ : form -> form -> form
val or_l : form list -> form
val imply : form -> form -> form
val equiv : form -> form -> form
val for_all : expr Var.t -> form -> form
val for_all_l : expr Var.t list -> form -> form
val exists : expr Var.t -> form -> form
val exists_l : expr Var.t list -> form -> form

(** {2 IO} *)

val print_set : ID.Set.t CCFormat.printer
val print_tuple : tuple CCFormat.printer
val print_expr : expr CCFormat.printer
val print_form : form CCFormat.printer
val print_decl : decl CCFormat.printer
val print_problem : problem CCFormat.printer

