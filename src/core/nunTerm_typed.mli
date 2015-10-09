
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

type ('a, 'ty) view = ('a, 'ty) NunTerm_intf.view

(** {2 Read-Only View} *)
module type VIEW = sig
  include NunTerm_intf.VIEW_SAME_TY

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : NunType_intf.S with type t = ty
end

(** {2 Full Signature} *)
module type S = sig
  include NunTerm_intf.VIEW_SAME_TY

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty
    include NunIntf.PRINT with type t := t

    val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  end

  val loc : t -> loc option

  val const : ?loc:loc -> ty:Ty.t -> id -> t
  val builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t
  val var : ?loc:loc -> Ty.t var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> ty var -> t -> t
  val let_ : ?loc:loc -> ty var -> t -> t -> t
  val ite : ?loc:loc -> t -> t -> t -> t
  val forall : ?loc:loc -> ty var -> t -> t
  val exists : ?loc:loc -> ty var -> t -> t
  val eq : ?loc:loc -> t -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunBuiltin.Ty.t -> Ty.t
  val ty_const : ?loc:loc -> id -> Ty.t
  val ty_var : ?loc:loc -> ty var -> Ty.t
  val ty_meta_var : ?loc:loc -> Ty.t NunMetaVar.t -> Ty.t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> ty var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

(** {2 Default Instance} *)

module Default : sig
  include S

  include NunTerm_ho.PRINT with type term = t and type ty := ty
end

val default : (module S with type t = Default.t)

(** {2 View as {!NunTerm_ho.VIEW}}

  Typed terms can be considered as regular higher-order terms, but
  only for reading — writing requires providing the type at every
  application *)

module AsHO(T : VIEW) : NunTerm_ho.VIEW
  with type t = T.t and type ty = T.ty

val as_ho : (module NunTerm_ho.VIEW with type t = Default.t)
