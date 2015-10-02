
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main Term Interface} *)

type var = NunVar.t

module Builtin : sig
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
  val equal : t -> t -> bool
end = struct
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
  let equal = (==)
end

type ('a, 'ty) view =
  | Builtin of Builtin.t (** built-in symbol *)
  | Var of var (** variable, bound or free *)
  | App of 'a * 'a list
  | Fun of var * 'ty * 'a
  | Forall of var * 'ty * 'a
  | Exists of var * 'ty * 'a
  | Let of var * 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunType_intf.Builtin.t (** Builtin type *)
  | TyArrow of 'ty * 'ty    (** Arrow type *)
  | TyForall of var * 'ty  (** Polymorphic/dependent type *)

(** {2 What is a term?} *)
module type S = sig
  type t
  (** Represents both terms and types *)

  module Ty : NunType_intf.AS_TERM with type term = t

  val view : t -> (t, Ty.t) view

  val build : (t, Ty.t) view -> t
end

module type S_WITH_UNIFIABLE_TY = sig
  type t

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t
    include NunType_intf.UNIFIABLE with type t := t
  end

  val view : t -> (t, Ty.t) view

  val build : (t, Ty.t) view -> t
end
