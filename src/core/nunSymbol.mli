
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Symbol}
  
  A symbol is a builtin constant that can have different representations
  in different syntaxes. For instance, [prop] and [not] are symbols. *)

type t = private
  | Prop
  | Type
  | Not
  | And
  | Or
  | True
  | False
  | Imply
  | Equiv

val prop : t
val type_ : t
val not_ : t
val and_ : t
val or_ : t
val true_ : t
val false_ : t
val imply : t
val equiv : t

include NunIntf.EQ with type t := t
include NunIntf.ORD with type t := t
include NunIntf.HASH with type t := t

include NunIntf.PRINT with type t := t
(** Pretty printing *)

val fixity : t -> [`Prefix | `Infix]

val to_string : t -> string



