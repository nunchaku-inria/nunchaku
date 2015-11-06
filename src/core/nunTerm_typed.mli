
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

type invariant = <meta:[`Meta]; poly: [`Poly]>

type 't repr = ('t, invariant) NunTerm_intf.repr

type 't build = ?loc:loc -> ty:'t -> ('t, invariant) view -> 't
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

module type REPR = sig
  type t
  val repr : t repr
  val ty: t -> t option
  val loc: t -> loc option
end

module type BUILD = sig
  type t
  val build : t build
  val kind : t (* impossible to build otherwise *)
end

module type S = sig
  type t
  include REPR with type t := t
  include BUILD with type t := t
end

(** {2 Utils} *)

module Util(T : S) : sig
  type t = T.t

  val view : t -> (t, invariant) view
  val ty: t -> t option
  val ty_exn : t -> t  (** @raise Not_found if there is not type *)
  val loc : t -> loc option

  val const : ?loc:loc -> ty:t -> id -> t
  val builtin : ?loc:loc -> ty:t -> NunBuiltin.T.t -> t
  val app_builtin : ?loc:loc -> ty:t -> NunBuiltin.T.t -> t list -> t
  val var : ?loc:loc -> t var -> t
  val app : ?loc:loc -> ty:t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:t -> t var -> t -> t
  val let_ : ?loc:loc -> t var -> t -> t -> t
  val match_with : ?loc:loc -> ty:t -> t -> t NunTerm_intf.cases -> t
  val ite : ?loc:loc -> t -> t -> t -> t
  val forall : ?loc:loc -> t var -> t -> t
  val exists : ?loc:loc -> t var -> t -> t
  val eq : ?loc:loc -> t -> t -> t

  val mk_bind :
    ?loc:loc ->
    ty:t ->
    NunMark.polymorph NunTerm_intf.binder ->
    t var ->
    t ->
    t

  val ty_type : t (** Type of types *)
  val ty_prop : t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunBuiltin.Ty.t -> t
  val ty_const : ?loc:loc -> id -> t
  val ty_var : ?loc:loc -> t var -> t
  val ty_meta_var : ?loc:loc -> t NunMetaVar.t -> t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> t -> t list -> t
  val ty_forall : ?loc:loc -> t var -> t -> t
  val ty_arrow : ?loc:loc -> t -> t -> t

  val as_ty : (t, invariant) NunType_intf.repr
  (** See a term as a type *)

  val is_ty: t -> bool
  (** [is_ty t] same as [is_Type (type of t)] *)
end

(** {2 Default Instance} *)

module Default : sig
  include S

  val print_funs : t NunTerm_ho.print_funs
end

(** {2 View as {!NunTerm_ho.VIEW}}

  Typed terms can be considered as regular higher-order terms, but
  only for reading — writing requires providing the type at every
  application *)

val as_ho : repr:'t repr -> ('t, invariant) NunTerm_ho.repr
