
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

module Builtin : sig
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

type ('a, 'ty) view =
  | Builtin of Builtin.t (** built-in symbol *)
  | Const of id (** top-level symbol *)
  | Var of 'ty var (** bound variable *)
  | App of 'a * 'a list
  | Fun of 'ty var * 'a
  | Forall of 'ty var * 'a
  | Exists of 'ty var * 'a
  | Let of 'ty var * 'a * 'a
  | TyKind
  | TyType
  | TyMeta of 'ty NunMetaVar.t
  | TyBuiltin of NunType_intf.Builtin.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)

(** {2 Read-Only View} *)
module type VIEW = sig
  type t

  type ty = private t

  val view : t -> (t, ty) view

  val ty : t -> ty option
  (** The type of a term *)
end

(** {2 Full Signature} *)
module type S = sig
  include VIEW

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty
    include NunIntf.PRINT with type t := t
  end

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val const : ?loc:loc -> ty:Ty.t -> id -> t
  val builtin : ?loc:loc -> ty:Ty.t -> Builtin.t -> t
  val var : ?loc:loc -> Ty.t var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> ty var -> t -> t
  val let_ : ?loc:loc -> ty var -> t -> t -> t
  val forall : ?loc:loc -> ty var -> t -> t
  val exists : ?loc:loc -> ty var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunType_intf.Builtin.t -> Ty.t
  val ty_const : ?loc:loc -> id -> Ty.t
  val ty_var : ?loc:loc -> ty var -> Ty.t
  val ty_meta_var : ?loc:loc -> Ty.t NunMetaVar.t -> Ty.t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> ty var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

(** {2 Print} *)

type 'a printer = Format.formatter -> 'a -> unit

module type PRINT = sig
  type term

  val print : term printer
  val print_in_app : term printer
  val print_in_binder : term printer
end

module Print(T : VIEW) : PRINT with type term = T.t

(** {2 Default Instance} *)

module Default : sig
  include S

  include PRINT with type term = t
end


