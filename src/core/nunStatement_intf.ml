
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-level Statements} *)

type var = NunVar.t

type ('term, 'ty) view =
  | Decl of var * 'ty  (** uninterpreted symbol *)
  | Def of var * 'term (** defined symbol *)
  | Axiom of 'term

module type S = sig
  type ('term,'ty) t

  val view : ('term,'ty) t -> ('term, 'ty) view
  val build : ('term,'ty) view -> ('term,'ty) t
end
