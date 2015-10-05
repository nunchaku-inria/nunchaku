
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-level Statements} *)

type id = NunID.t

type ('term, 'ty) view =
  | Decl of id * 'ty (** uninterpreted symbol *)
  | Def of id * 'ty * 'term (** defined symbol *)
  | Axiom of 'term

module type S = sig
  type ('term,'ty) t

  val view : ('term,'ty) t -> ('term, 'ty) view
  val build : ('term,'ty) view -> ('term,'ty) t
end
