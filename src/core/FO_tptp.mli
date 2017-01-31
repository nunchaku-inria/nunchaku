
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 TPTP representation}

    Representation of terms and formulas for FOF (untyped TPTP) *)

type ty = Unitype
type var = ty Var.t

type term =
  | App of ID.t * term list
  | Var of var
  | True
  | False
  | Undefined_atom of term list

type form =
  | And of form list
  | Or of form list
  | Not of form
  | Imply of form * form
  | Equiv of form * form
  | Atom of term
  | Eq of term * term
  | Neq of term * term
  | Forall of var * form
  | Exists of var * form

type role =
  | R_axiom
  | R_conjecture

type statement = {
  st_name: string;
  st_role: role;
  st_form: form;
}

type problem = {
  pb_statements: statement CCVector.ro_vector;
  pb_meta: ProblemMetadata.t;
}

(** {2 Basics} *)

val const : ID.t -> term
val app : ID.t -> term list -> term
val var : var -> term
val undefined_atom : term list -> term
val true_ : term
val false_ : term

val term_equal : term -> term -> bool
val term_hash : term -> int

val and_ : form list -> form
val or_ : form list -> form
val imply : form -> form -> form
val equiv : form -> form -> form
val atom : term -> form
val not_ : form -> form
val eq : term -> term -> form
val neq : term -> term -> form
val forall : var -> form -> form
val forall_l : var list -> form -> form
val exists : var -> form -> form
val exists_l : var list -> form -> form

val axiom : ?name:string -> form -> statement
val conjecture : ?name:string -> form -> statement

(** {2 IO} *)

val erase : ID.Erase.state
(** Used to map IDs to names during printing *)

val pp_role_tptp : role CCFormat.printer
val pp_term_tptp : term CCFormat.printer
val pp_form_tptp : form CCFormat.printer
val pp_statement_tptp : statement CCFormat.printer
val pp_problem_tptp : problem CCFormat.printer

