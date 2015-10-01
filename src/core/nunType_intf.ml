
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type var = NunVar.t
type symbol = NunSymbol.t

type 'a view =
  | Sym of symbol (** Builtin type *)
  | Var of var
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of var * 'a  (** Polymorphic type *)

(** A concrete type *)
module type S = sig
  type t

  val view : t -> t view

  val build : t view -> t
end
