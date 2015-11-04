
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a printer = Format.formatter -> 'a -> unit

type ('a, 'inv) view =
  | Builtin of NunBuiltin.Ty.t (** Builtin type *)
  | Const of id
  | Var :
      'a var (** Constant or bound variable *)
      -> ('a, <poly:NunMark.polymorph;..>) view
  | Meta :
      'a NunMetaVar.t (** Meta-variable, used for unification *)
      -> ('a, <meta: NunMark.with_meta;..>) view
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall :   (** Polymorphic type *)
      'a var
      * 'a
      -> ('a, <poly: NunMark.polymorph;..>) view

(** {2 Basic Interface} *)
module type S = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  type t

  val view : t -> (t, invariant) view
  (** View must follow {!deref} pointers *)
end

module type UTILS = sig
  type t
  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val returns : t -> t (** follow forall/arrows to get return type.  *)
  val is_Kind : t -> bool (** type == Kind? *)
  val to_seq : t -> t Sequence.t
end

module type AS_TERM = sig
  type term
  type t = term

  include S with type t := t
  include UTILS with type t := t
end

module type PRINTABLE = sig
  include S
  include NunIntf.PRINT with type t := t
end

(** {2 Utils} *)
module Utils(Ty : S) : UTILS with type t = Ty.t

(** {2 Print Types} *)

module Print(Ty : S) : sig
  val print : Ty.t printer
  val print_in_app : Ty.t printer
  val print_in_arrow : Ty.t printer
end
