
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

type invariant = <meta:NunMark.with_meta; poly: NunMark.polymorph>

type 't repr = {
  repr: ('t, invariant) NunTerm_intf.repr;
  ty: 't -> 't option;
  loc: 't -> loc option;
}

type 't build = {
  b_repr: 't repr;
  b_build: ?loc:loc -> ty:'t -> ('t, invariant) view -> 't;
  b_kind: 't;
}
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

(** {2 Utils} *)

val view : repr:'t repr -> 't -> ('t, invariant) view
val ty: repr:'t repr -> 't -> 't option
val ty_exn : repr:'t repr -> 't -> 't  (** @raise Not_found if there is not type *)
val loc : repr:'t repr -> 't -> loc option
val build : build:'t build -> ?loc:loc -> ty:'t -> ('t, invariant) view -> 't

val const : build:'t build -> ?loc:loc -> ty:'t -> id -> 't
val builtin : build:'t build -> ?loc:loc -> ty:'t -> NunBuiltin.T.t -> 't
val app_builtin : build:'t build -> ?loc:loc -> ty:'t -> NunBuiltin.T.t -> 't list -> 't
val var : build:'t build -> ?loc:loc -> 't var -> 't
val app : build:'t build -> ?loc:loc -> ty:'t -> 't -> 't list -> 't
val fun_ : build:'t build -> ?loc:loc -> ty:'t -> 't var -> 't -> 't
val let_ : build:'t build -> ?loc:loc -> 't var -> 't -> 't -> 't
val match_with : build:'t build -> ?loc:loc -> ty:'t -> 't -> 't NunTerm_intf.cases -> 't
val ite : build:'t build -> ?loc:loc -> 't -> 't -> 't -> 't
val forall : build:'t build -> ?loc:loc -> 't var -> 't -> 't
val exists : build:'t build -> ?loc:loc -> 't var -> 't -> 't
val eq : build:'t build -> ?loc:loc -> 't -> 't -> 't

val mk_bind :
  build:'t build ->
  ?loc:loc ->
  ty:'t ->
  NunMark.polymorph NunTerm_intf.binder ->
  't var ->
  't ->
  't

val ty_type : build:'t build -> 't (** Type of types *)
val ty_prop : build:'t build -> 't (** Propositions *)

val ty_builtin : build:'t build -> ?loc:loc -> NunBuiltin.Ty.t -> 't
val ty_const : build:'t build -> ?loc:loc -> id -> 't
val ty_var : build:'t build -> ?loc:loc -> 't var -> 't
val ty_meta_var : build:'t build -> ?loc:loc -> 't NunMetaVar.t -> 't  (** Meta-variable, ready for unif *)
val ty_app : build:'t build -> ?loc:loc -> 't -> 't list -> 't
val ty_forall : build:'t build -> ?loc:loc -> 't var -> 't -> 't
val ty_arrow : build:'t build -> ?loc:loc -> 't -> 't -> 't

val as_ty : repr:'t repr -> ('t, invariant) NunType_intf.repr
(** See a term as a type *)

val is_ty: repr:'t repr -> 't -> bool
(** [is_ty t] same as [is_Type (type of t)] *)

(** {2 Default Instance} *)

type default

val default_repr : default repr
val default_build : default build
val default_print : default NunTerm_ho.print_funs

(** {2 View as {!NunTerm_ho.VIEW}}

  Typed terms can be considered as regular higher-order terms, but
  only for reading — writing requires providing the type at every
  application *)

val as_ho : repr:'t repr -> ('t, invariant) NunTerm_ho.repr
