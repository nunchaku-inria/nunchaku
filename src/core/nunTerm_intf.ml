
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main Term Interface} *)

type var = NunVar.t
type symbol = NunSymbol.t

type ('a, 'ty) view =
  | Sym of symbol (** built-in symbol *)
  | Var of var (** variable, bound or free *)
  | App of 'a * 'ty list * 'a list
  | Fun of var * 'ty * 'a
  | Forall of var * 'ty * 'a
  | Exists of var * 'ty * 'a
  | Let of var * 'a * 'a

(** {2 What is a term?} *)
module type S = sig
  type t

  type ty
  (** Some terms contain types, for instance in functions *)

  val view : t -> (t, ty) view

  val build : (t, ty) view -> t
end

