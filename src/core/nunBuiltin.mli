
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtin Symbols} *)

module Ty : sig
  type t =
    | Prop
  val equal : t -> t -> bool
  val to_string : t -> string
end

module T : sig
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
    | Eq
  val fixity : t -> [`Infix | `Prefix]
  val to_string : t -> string
  val equal : t -> t -> bool
end
