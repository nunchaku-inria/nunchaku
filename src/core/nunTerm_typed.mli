
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

type ('t,'inv) repr = ('t, 'inv) NunTerm_intf.repr

type ('t,'inv) build = ?loc:loc -> ty:'t -> ('t, 'inv) view -> 't
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

module type REPR = sig
  type 'i t
  val repr : ('i t,'i) repr
  val ty: 'i t -> 'i t option
  val loc: _ t -> loc option
end

module type BUILD = sig
  type 'i t
  val build : ('i t, 'i) build
  val kind : unit -> 'i t (* impossible to build otherwise *)
end

module type S = sig
  type 'i t
  include REPR with type 'i t := 'i t
  include BUILD with type 'i t := 'i t
end

(** {2 Utils} *)

module Util(T : S) : sig
  type 'i t = 'i T.t

  val view : 'i t -> ('i t, 'i) view
  val ty: 'i t -> 'i t option
  val ty_exn : 'i t -> 'i t  (** @raise Not_found if there is not type *)
  val loc : _ t -> loc option

  val const : ?loc:loc -> ty:'i t -> id -> 'i t
  val builtin : ?loc:loc -> ty:'i t -> NunBuiltin.T.t -> 'i t
  val app_builtin : ?loc:loc -> ty:'i t -> NunBuiltin.T.t -> 'i t list -> 'i t
  val var : ?loc:loc -> 'i t var -> 'i t
  val app : ?loc:loc -> ty:'i t -> 'i t -> 'i t list -> 'i t
  val fun_ : ?loc:loc -> ty:(<poly:_;..> as 'i) t -> 'i t var -> 'i t -> 'i t
  val let_ : ?loc:loc -> 'i t var -> 'i t -> 'i t -> 'i t
  val match_with : ?loc:loc -> ty:'i t -> 'i t -> 'i t NunTerm_intf.cases -> 'i t
  val ite : ?loc:loc -> 'i t -> 'i t -> 'i t -> 'i t
  val forall : ?loc:loc -> (<poly:_;..> as 'i) t var -> 'i t -> 'i t
  val exists : ?loc:loc -> (<poly:_;..> as 'i) t var -> 'i t -> 'i t
  val eq : ?loc:loc -> 'i t -> 'i t -> 'i t

  val mk_bind :
    ?loc:loc ->
    ty:(<poly:'inv_p;..> as 'i) t ->
    'inv_p NunTerm_intf.binder -> 'i t var -> 'i t -> 'i t

  val ty_type : unit -> 'i t (** Type of types *)
  val ty_prop : unit -> 'i t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunBuiltin.Ty.t -> 'i t
  val ty_const : ?loc:loc -> id -> 'i t
  val ty_app : ?loc:loc -> 'i t -> 'i t list -> 'i t
  val ty_arrow : ?loc:loc -> 'i t -> 'i t -> 'i t

  val ty_var : ?loc:loc -> (<poly:[`Poly];..> as 'i) t var -> 'i t
  val ty_forall : ?loc:loc -> (<poly:[`Poly];..> as 'i) t var -> 'i t -> 'i t

  val ty_meta_var :
    ?loc:loc ->
    (<meta:[`Meta];poly:_> as 'i)  t NunMetaVar.t ->
    'i t  (** Meta-variable, ready for unif *)

  val as_ty : ('i t, 'i) NunType_intf.repr
  (** See a term as a type *)

  val is_ty: _ t -> bool
  (** [is_ty t] same as [is_Type (type of t)] *)
end

(** {2 Default Instance} *)

module Default : sig
  include S

  val print_funs : unit -> _ t NunTerm_ho.print_funs
end

(** {2 View as {!NunTerm_ho.VIEW}}

  Typed terms can be considered as regular higher-order terms, but
  only for reading — writing requires providing the type at every
  application *)

module AsHO(T : REPR) : NunTerm_ho.REPR with type 'a t = 'a T.t
