
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Relational FO Logic}

    This corresponds, roughly, to Kodkod's logic *)

(** {2 Types} *)

type atom_name = ID.t

(* the portion of the universe concerned with this atom name *)
type sub_universe = {
  su_name: atom_name;
  su_card: int;
}

(* an indexed atom. It lives in the sub-universe of the same name *)
type atom = {
  a_sub_universe: sub_universe;
  a_index: int; (* invariant: a_index < a_sub_universe.su_card *)
}

type tuple = atom list

type tuple_set = private
  | TS_list of tuple list (* explicit set *)
  | TS_product of tuple_set list (* cartesian product *)
  | TS_all of sub_universe (* all the atoms of this sub-universe *)

type unop =
  | Flip (** flip p x y <=> p y x *)
  | Trans (** trans p == transitive closure *)

type binop =
  | Union
  | Inter
  | Diff
  | Join (** join (x,y) (y,z) == (x,z) *)
  | Product (** product (x1,y1) (x2,y2) == (x1,y1,x2,y2) *)

(** multiplicity *)
type mult =
  | M_no
  | M_one (* exactly 1 *)
  | M_lone (* 0 or 1 *)
  | M_some (* at least 1 *)

type expr =
  | None_ (* empty set *)
  | Const of ID.t
  | Tuple_set of tuple_set
  | Var of expr Var.t
  | Unop of unop * expr
  | Binop of binop * expr * expr
  | If of form * expr * expr
  | Comprehension of expr Var.t * form

and form =
  | True
  | False
  | Eq of expr * expr
  | In of expr * expr
  | Mult of mult * expr
  | Not of form
  | And of form * form
  | Or of form * form
  | Equiv of form * form
  | Forall of expr Var.t * form
  | Exists of expr Var.t * form

type decl = {
  decl_id: ID.t;
  decl_arity: int;
  decl_low: tuple_set; (* lower bound *)
  decl_high: tuple_set; (* higher bound *)
}

(** A universe is a list of sub-universes, each with a different name *)
type universe = sub_universe list

type problem = private {
  pb_univ: universe;
  pb_decls: decl CCVector.ro_vector;
  pb_goal: form list; (* conjunction *)
  pb_meta: ProblemMetadata.t;
}

(** {2 Helpers} *)

val unop : unop -> expr -> expr
val binop : binop -> expr -> expr -> expr
val mult : mult -> expr -> form

val su_make : ID.t -> card:int -> sub_universe
val su_equal : sub_universe -> sub_universe -> bool
val su_hash : sub_universe -> int
val su_compare : sub_universe -> sub_universe -> int

val ts_list : tuple list -> tuple_set
val ts_all : sub_universe -> tuple_set
val ts_product : tuple_set list -> tuple_set
(** Cartesian product of given tuples
    @raise Invalid_argument if the list is empty *)

val flip : expr -> expr
val trans : expr -> expr
val const : ID.t -> expr
val var : expr Var.t -> expr
val tuple_set : tuple_set -> expr
val union : expr -> expr -> expr
val inter : expr -> expr -> expr
val diff : expr -> expr -> expr
val join : expr -> expr -> expr
val product : expr -> expr -> expr
val if_ : form -> expr -> expr -> expr
val comprehension : expr Var.t -> form -> expr

val true_ : form
val false_ : form
val eq : expr -> expr -> form
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

val mk_problem :
  meta:ProblemMetadata.t ->
  univ:universe ->
  decls:decl CCVector.ro_vector ->
  goal:form list ->
  problem

(** {2 IO} *)

val print_atom : atom CCFormat.printer
val print_tuple : tuple CCFormat.printer
val print_tuple_set : tuple_set CCFormat.printer
val print_sub_universe : sub_universe CCFormat.printer
val print_universe : universe CCFormat.printer
val print_expr : expr CCFormat.printer
val print_form : form CCFormat.printer
val print_decl : decl CCFormat.printer
val print_problem : problem CCFormat.printer

