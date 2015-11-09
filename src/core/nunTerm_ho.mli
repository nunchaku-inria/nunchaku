
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
  type 'inv t
  val repr : ('inv t,'inv) repr
end

module type BUILD = sig
  type 'inv t
  val build : ('inv t,'inv) build
end

module type S = sig
  type 'inv t
  include REPR with type 'a t := 'a t
  include BUILD with type 'a t := 'a t
end

(** {2 Packed Term}

  A term packed with its representation *)

type packed = Packed : 't * ('t, _) repr -> packed

val pack : repr:('t, _) repr -> 't -> packed

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

val ty_var : build:('t, <poly:[`Poly];..> as 'inv) build -> 't var -> 't
val ty_forall : build:('t, <poly:[`Poly];..> as 'inv) build -> 't var -> 't -> 't

module Util(T : S) : sig
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

  val ty_type : unit -> 'inv T.t (** Type of types *)
  val ty_kind : unit -> 'inv T.t (** Type of ty_type *)
  val ty_prop : unit -> 'inv T.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> 'inv T.t
  val ty_const : id -> 'inv T.t
  val ty_app : 'inv T.t -> 'inv T.t list -> 'inv T.t
  val ty_arrow : 'inv T.t -> 'inv T.t -> 'inv T.t

  val ty_var : (<poly:[`Poly];..> as 'inv) T.t var -> 'inv T.t
  val ty_forall : (<poly:[`Poly];..> as 'inv) T.t var -> 'inv T.t -> 'inv T.t

  val as_ty : ('inv T.t, 'inv) NunType_intf.repr
  val pack: 'inv T.t -> packed
end

(** {2 Default Implementation} *)

module Default : S
(** Default representation for terms *)

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

module SubstUtil(T : S) : sig
  type 'i subst = ('i T.t, 'i T.t) NunVar.Subst.t

  val equal : subst:'inv subst -> 'inv T.t -> 'inv T.t -> bool
  (** Equality modulo substitution *)

  val deref : subst:'inv subst -> 'inv T.t -> 'inv T.t
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  val eval : subst:'inv subst -> 'inv T.t -> 'inv T.t
  (** Applying a substitution *)

  exception ApplyError of string * packed * packed list
  (** Raised when a type application fails *)
  (* TODO get rid of packed? *)

  val ty_apply_full : 'inv T.t -> 'inv T.t list -> 'inv T.t * 'inv subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  val ty_apply : 'inv T.t -> 'inv T.t list -> 'inv T.t
  (** [apply t l] computes the type of [f args] where [f : t] and [args : l].
      @raise ApplyError if the arguments do not match *)

  type 'inv signature = id -> 'inv T.t option
  (** A signature is a way to obtain the type of a variable *)

  val ty :
    sigma:'inv signature ->
    (<poly:[`Poly];meta:'m> as 'inv) T.t ->
    'inv T.t or_error
  (** Compute the type of the given term in the given signature. *)

  val ty_exn :
    sigma:'inv signature ->
    (<poly:[`Poly];meta:'m> as 'inv) T.t ->
    'inv T.t
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Undefined in case some symbol is not defined *)

  exception UnifError of string * packed * packed
  (** Raised for unification or matching errors *)

  val match_exn : ?subst2:'inv subst -> 'inv T.t -> 'inv T.t -> 'inv subst
  (** [match_exn ~subst2 t1 t2] matches the pattern [t1] against [subst2 t2].
      Variables in [subst2 t2] are not bound.
      We assume [t1] and [subst2 t2] do not share variables, and we assume
      that [t1] is a mostly first-order {b pattern} (no binders, but variables
      in head position is accepted and will only match an application).
      @raise UnifError if they don'inv T.t match
      @raise Invalid_argument if [t1] is not a valid pattern *)

  val match_ : ?subst2:'inv subst -> 'inv T.t -> 'inv T.t -> 'inv subst option
  (** Safe version of {!match_exn}
      @raise Invalid_argument if [t1] is not a valid pattern *)

  (* TODO: unification *)
end

(** {2 Conversion to FO Terms} *)

type to_fo_invariant = <poly:[`Mono]; meta:[`NoMeta]>

module ToFO(FO : NunFO.S) : sig
  exception NotInFO of string * packed
  (** Raised if a term is not in the first-order fragment *)

  type invariant = to_fo_invariant

  val convert_problem :
    repr:('t1,invariant) repr ->
    ('t1,'t1,_) NunProblem.t ->
    (FO.Formula.t,FO.T.t,FO.Ty.t) NunFO.Problem.t
  (** Convert a problem in HO representation to a FO representation
      @raise NotInFO if some terms in the input problem are not regular
        first-order terms. *)
end

(** {2 Convert FO to HO} *)

module OfFO(T:S)(FO : NunFO.VIEW) : sig
  type t = to_fo_invariant T.t

  val convert_ty : FO.Ty.t -> t

  val convert_term : FO.T.t -> t

  val convert_formula : FO.Formula.t -> t

  val convert_model : FO.term_or_form NunModel.t -> t NunModel.t
end

module TransFO(T1 : S)(T2 : NunFO.S) : sig
  val pipe : unit ->
    ((to_fo_invariant T1.t, to_fo_invariant T1.t, _) NunProblem.t,
      (T2.Formula.t, T2.T.t, T2.Ty.t) NunFO.Problem.t,
      (T2.T.t,T2.Formula.t) NunFO.term_or_form NunModel.t,
      to_fo_invariant T1.t NunModel.t
    ) NunTransform.t

  val pipe_with :
    decode:('b -> 'c) ->
    ((to_fo_invariant T1.t, to_fo_invariant T1.t, _) NunProblem.t,
      (T2.Formula.t, T2.T.t, T2.Ty.t) NunFO.Problem.t,
      'b, 'c
    ) NunTransform.t
end

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

  type invariant = <meta:[`NoMeta]; poly:[`Poly]>

  val convert_term : build:('t,invariant) build -> NunUntypedAST.term -> 't
end
