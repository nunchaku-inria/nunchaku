
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'inv) repr = ('t, 'inv) NunTerm_intf.repr

type ('t, 'inv) build = ('t, 'inv) NunTerm_intf.build

val as_ty : repr:('t, 'inv) repr -> ('t, 'inv) NunType_intf.repr
(** View of a term as a type. *)

module type REPR = sig
  type +'inv t
  val repr : ('inv t,'inv) repr
end

module type BUILD = sig
  type +'inv t
  val build : ('inv t,'inv) build
end

(** {2 Utils} *)

val const : build:('t, 'inv) build -> id -> 't
val builtin : build:('t, 'inv) build -> NunBuiltin.T.t -> 't
val app_builtin : build:('t, 'inv) build -> NunBuiltin.T.t -> 't list -> 't
val var : build:('t, 'inv) build -> 't var -> 't
val app : build:('t, 'inv) build -> 't -> 't list -> 't
val fun_ : build:('t, <poly:_;..>) build -> 't var -> 't -> 't
val let_ : build:('t, 'inv) build -> 't var -> 't -> 't -> 't
val match_with : build:('t, 'inv) build -> 't -> 't NunTerm_intf.cases -> 't
val ite : build:('t, 'inv) build -> 't -> 't -> 't -> 't
val forall : build:('t, <poly:_;..>) build -> 't var -> 't -> 't
val exists : build:('t, <poly:_;..>) build -> 't var -> 't -> 't
val eq : build:('t, 'inv) build -> 't -> 't -> 't

val mk_bind :
  build:('t, <poly:'poly;..> as 'inv) build ->
  'poly NunTerm_intf.binder ->
  't var -> 't -> 't

val ty_type : build:('t, 'inv) build -> 't (** Type of types *)
val ty_kind : build:('t, 'inv) build -> 't (** Type of ty_type *)
val ty_prop : build:('t, 'inv) build -> 't (** Propositions *)

val ty_builtin : build:('t, 'inv) build -> NunBuiltin.Ty.t -> 't
val ty_const : build:('t, 'inv) build ->id -> 't
val ty_app : build:('t, 'inv) build -> 't -> 't list -> 't
val ty_arrow : build:('t, 'inv) build -> 't -> 't -> 't

val ty_var : build:('t, <poly:NunMark.polymorph;..> as 'inv) build -> 't var -> 't
val ty_forall : build:('t, <poly:NunMark.polymorph;..> as 'inv) build -> 't var -> 't -> 't

module Util(T : BUILD) : sig
  val const : id -> 'inv T.t
  val builtin : NunBuiltin.T.t -> 'inv T.t
  val app_builtin : NunBuiltin.T.t -> 'inv T.t list -> 'inv T.t
  val var : 'inv T.t var -> 'inv T.t
  val app : 'inv T.t -> 'inv T.t list -> 'inv T.t
  val fun_ : (<poly:_;..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t
  val let_ : 'inv T.t var -> 'inv T.t -> 'inv T.t -> 'inv T.t
  val match_with : 'inv T.t -> 'inv T.t NunTerm_intf.cases -> 'inv T.t
  val ite : 'inv T.t -> 'inv T.t -> 'inv T.t -> 'inv T.t
  val forall : (<poly:_;..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t
  val exists : (<poly:_;..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t
  val eq : 'inv T.t -> 'inv T.t -> 'inv T.t

  val mk_bind :
    'inv_p NunTerm_intf.binder ->
    (<poly:'inv_p;..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t

  val ty_type : 'inv T.t (** Type of types *)
  val ty_kind : 'inv T.t (** Type of ty_type *)
  val ty_prop : 'inv T.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> 'inv T.t
  val ty_const : id -> 'inv T.t
  val ty_app : 'inv T.t -> 'inv T.t list -> 'inv T.t
  val ty_arrow : 'inv T.t -> 'inv T.t -> 'inv T.t

  val ty_var : (<poly:NunMark.polymorph;..> as 'inv) T.t var -> 'inv T.t
  val ty_forall : (<poly:NunMark.polymorph;..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t
end

(** {2 Default Implementation} *)

type 'inv default
(** Default representation for terms *)

val default_repr : ('inv default, 'inv) repr
val default_build : ('inv default, 'inv) build

(** {2 Printing} *)

type 't print_funs = {
  print : 't printer;
  print_in_app : 't printer;
  print_in_binder : 't printer;
  print_ty : 't printer;
}

val mk_print: repr:('t, _) repr -> 't print_funs

val print : repr:('t, _) repr -> 't printer
val print_in_app : repr:('t, _) repr -> 't printer
val print_in_binder : repr:('t, _) repr -> 't printer
val print_ty : repr:('t, _) repr -> 't printer

(** {2 Packed Term}

  A term packed with its representation *)

type packed = Packed : 't * ('t, _) repr -> packed

val pack : repr:('t, _) repr -> 't -> packed

(** {2 Type Erasure} *)

module Erase : sig
  module Untyped = NunUntypedAST

  type ctx
  (** Disambiguation context *)

  val create : unit -> ctx
  (** New context for the given term representation *)

  val erase : repr:('t, _) repr -> ctx:ctx -> 't -> Untyped.term

  val erase_ty : repr:('t, _) repr -> ctx:ctx -> 't -> Untyped.ty
end

(** {2 Substitutions} *)

exception Undefined of id
(** When a symbol is not defined *)

module SubstUtil : sig
  type 't subst = ('t, 't) NunVar.Subst.t

  val equal : build:('t,_) build -> subst:'t subst -> 't -> 't -> bool
  (** Equality modulo substitution *)

  val deref : repr:('t,_) repr -> subst:'t subst -> 't -> 't
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  val eval : build:('t,_) build -> subst:'t subst -> 't -> 't
  (** Applying a substitution *)

  exception ApplyError of string * packed * packed list
  (** Raised when a type application fails *)

  val ty_apply_full : build:('t,_) build -> 't -> 't list -> 't * 't subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  val ty_apply : build:('t,_) build -> 't -> 't list -> 't
  (** [apply t l] computes the type of [f args] where [f : t] and [args : l].
      @raise ApplyError if the arguments do not match *)

  type 't signature = 't NunSignature.t

  val ty : build:('t,<poly:NunMark.polymorph;meta:'m>) build ->
           sigma:'t signature -> 't -> 't or_error
  (** Compute the type of the given term in the given signature. *)

  val ty_exn : build:('t,<poly:NunMark.polymorph;meta:'m>) build ->
               sigma:'t signature -> 't -> 't
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Undefined in case some symbol is not defined *)

  exception UnifError of string * packed * packed
  (** Raised for unification or matching errors *)

  val match_exn : build:('t, _) build -> ?subst2:'t subst -> 't -> 't -> 't subst
  (** [match_exn ~subst2 t1 t2] matches the pattern [t1] against [subst2 t2].
      Variables in [subst2 t2] are not bound.
      We assume [t1] and [subst2 t2] do not share variables, and we assume
      that [t1] is a mostly first-order {b pattern} (no binders, but variables
      in head position is accepted and will only match an application).
      @raise UnifError if they don't match
      @raise Invalid_argument if [t1] is not a valid pattern *)

  val match_ : build:('t, _) build -> ?subst2:'t subst -> 't -> 't -> 't subst option
  (** Safe version of {!match_exn}
      @raise Invalid_argument if [t1] is not a valid pattern *)

  (* TODO: unification *)
end

(** {2 Conversion to FO Terms} *)

type to_fo_invariant = <poly:NunMark.monomorph; meta:NunMark.without_meta>

module ToFO(FO : NunFO.S) : sig
  exception NotInFO of string * packed
  (** Raised if a term is not in the first-order fragment *)

  type invariant = to_fo_invariant

  val convert_problem :
    repr:('t1,invariant) repr ->
    ('t1,'t1,NunMark.linear) NunProblem.t ->
    (FO.Formula.t,FO.T.t,FO.Ty.t) NunFO.Problem.t
  (** Convert a problem in HO representation to a FO representation
      @raise NotInFO if some terms in the input problem are not regular
        first-order terms. *)
end

(** {2 Convert FO to HO} *)

module OfFO(FO : NunFO.VIEW) : sig
  val convert_ty :
    build:('t,_) build ->
    FO.Ty.t ->
    't

  val convert_term :
    build:('t,<poly:_;..>) build ->
    FO.T.t ->
    't

  val convert_formula :
    build:('t,<poly:_;..>) build ->
    FO.Formula.t ->
    't

  val convert_model :
    build:('t,<poly:_;..>) build ->
    FO.term_or_form NunModel.t ->
    't NunModel.t
end

val to_fo :
  build1:('t1, to_fo_invariant) build ->
  build2:('f2,'t2,'ty2) NunFO.build ->
  (('t1, 't1, NunMark.linear) NunProblem.t,
    ('f2, 't2, 'ty2) NunFO.Problem.t,
    ('t2,'f2) NunFO.term_or_form NunModel.t,
    't1 NunModel.t
  ) NunTransform.t

val to_fo_no_model :
  repr1:('t1, to_fo_invariant) repr ->
  build2:('f2,'t2,'ty2) NunFO.build ->
  (('t1, 't1, NunMark.linear) NunProblem.t,
    ('f2, 't2, 'ty2) NunFO.Problem.t,
    'b, 'b
  ) NunTransform.t

(** {2 Conversion}

  Direct conversion between two representations *)

val convert :
  repr1:('t1,'inv) repr ->
  build2:('t2,'inv) build ->
  't1 ->
  't2

(** {2 Conversion of UntypedAST to HO, without Type-Checking}

  This should be useful mostly for tests: parse and convert a term to a usable
  format in a simple way *)

module OfUntyped : sig
  exception Error of NunUntypedAST.term * string

  type invariant = <meta:NunMark.without_meta; poly:NunMark.polymorph>

  val convert_term : build:('t,invariant) build -> NunUntypedAST.term -> 't
end
