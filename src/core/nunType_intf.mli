
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t

type 'a view =
  | Kind (** the "type" of [Type], in some sense *)
  | Type (** the type of types *)
  | Builtin of NunBuiltin.Ty.t (** Builtin type *)
  | Const of id
  | Var of 'a var (** Constant or bound variable *)
  | Meta of 'a NunMetaVar.t (** Meta-variable, used for unification *)
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of 'a var * 'a  (** Polymorphic type *)

(** {2 Basic Interface} *)
module type S = sig
  type t

  val view : t -> t view
  (** View must follow {!deref} pointers *)
end

module type AS_TERM = sig
  type term
  type t = term

  include S with type t := t

  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val returns : t -> t (** follow forall/arrows to get return type.  *)
  val is_Kind : t -> bool (** type == Kind? *)
end

module type PRINTABLE = sig
  include S
  include NunIntf.PRINT with type t := t
end

(** {2 Print Types} *)

type 'a printer = Format.formatter -> 'a -> unit

module Print(Ty : S) : sig
  val print : Ty.t printer
  val print_in_app : Ty.t printer
  val print_in_arrow : Ty.t printer
end
