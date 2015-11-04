
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

module type POLY_VIEW = sig
  include NunTerm_intf.VIEW

  module Ty : sig
    type 'i t = 'i ty
    val view : 'i t -> ('i t,'i) NunType_intf.view
  end
end

module type VIEW = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  type t
  type ty = t

  val view : t -> (t, invariant) NunTerm_intf.view

  module Ty : sig
    type t = ty
    val view : t -> (t,invariant) NunType_intf.view
  end
end

module type S = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  val poly : invariant_poly NunMark.poly_witness

  type t
  type ty = t

  val view : t -> (t, invariant) NunTerm_intf.view
  val build : (t, invariant) NunTerm_intf.view -> t

  module Ty : NunType_intf.AS_TERM
    with type term = t and type t = ty
    and type invariant_poly = invariant_poly
    and type invariant_meta = invariant_meta

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val app_builtin : NunBuiltin.T.t -> t list -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val match_with : t -> t NunTerm_intf.cases -> t
  val ite : t -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t
  val eq : t -> t -> t

  val mk_bind : invariant_poly NunTerm_intf.binder -> Ty.t var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_kind : Ty.t (** Type of ty_type *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t
end

module type S_POLY = sig
  type invariant_meta
  include S
    with type invariant_poly = NunMark.polymorph
    and type invariant_meta := invariant_meta

  val ty_var : ty var -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
end

module DefaultPoly
  : S_POLY
  with type invariant_poly = NunMark.polymorph
  and type invariant_meta = NunMark.without_meta

module DefaultMono
  : S
  with type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta

val default_poly :
  (module S with type t = DefaultPoly.t
  and type invariant_poly = NunMark.polymorph
  and type invariant_meta = NunMark.without_meta)

val default_mono :
  (module S with type t = DefaultMono.t
  and type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta)

(** {2 Printing} *)

module type PRINT = sig
  type term
  type ty = term

  val print : term printer
  val print_in_app : term printer
  val print_in_binder : term printer

  val print_ty : ty printer
end

module Print(T : VIEW) : PRINT with type term = T.t and type ty = T.ty

(** {2 Type Erasure} *)

module Erase(T : VIEW) : sig
  module Untyped = NunUntypedAST

  type ctx
  (** Disambiguation context *)

  val create : unit -> ctx
  (** New context *)

  val erase : ctx:ctx -> T.t -> Untyped.term

  val erase_ty : ctx:ctx -> T.ty -> Untyped.ty
end

(** {2 Substitutions} *)

exception Undefined of id
(** When a symbol is not defined *)

module SubstUtil(T : S)(Subst : NunVar.SUBST with type ty = T.ty) : sig
  type subst = T.t Subst.t

  val equal : subst:subst -> T.t -> T.t -> bool
  (** Equality modulo substitution *)

  val deref : subst:subst -> T.t -> T.t
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  val eval : subst:subst -> T.t -> T.t
  (** Applying a substitution *)

  exception ApplyError of string * T.t * T.t list
  (** Raised when a type application fails *)

  val ty_apply : T.ty -> T.t list -> T.ty
  (** [apply t l] computes the type of [f args] where [f : t] and [args : l]
      @raise ApplyError if the arguments do not match *)

  val ty_apply_full : T.ty -> T.t list -> T.ty * subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  type signature = T.ty NunSignature.t

  val ty : sigma:signature -> T.t -> T.ty or_error
  (** Compute the type of the given term in the given signature.
      @param poly an explicit witness of whether polymorphism is allowed
        (necessary to compute the type of a function... or fail) *)

  val ty_exn : sigma:signature -> T.t -> T.ty
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Undefined in case some symbol is not defined *)

  exception UnifError of string * T.t * T.t
  (** Raised for unification or matching errors *)

  val match_exn : ?subst2:subst -> T.t -> T.t -> subst
  (** [match_exn ~subst2 t1 t2] matches the pattern [t1] against [subst2 t2].
      Variables in [subst2 t2] are not bound.
      We assume [t1] and [subst2 t2] do not share variables, and we assume
      that [t1] is a mostly first-order {b pattern} (no binders, but variables
      in head position is accepted and will only match an application).
      @raise UnifError if they don't match
      @raise Invalid_argument if [t1] is not a valid pattern *)

  val match_ : ?subst2:subst -> T.t -> T.t -> subst option
  (** Safe version of {!match_exn}
      @raise Invalid_argument if [t1] is not a valid pattern *)

  (* TODO: unification *)
end

(** {2 Conversion to FO Terms} *)

module ToFO(T : S
  with type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta
)(T2 : NunFO.S) : sig
  type term = T.t
  type ty = T.ty

  exception NotInFO of string * term
  (** Raised if a term is not in the first-order fragment *)

  (** Convert a problem to a FO problem *)
  val convert_problem :
    (term, ty, NunMark.linear) NunProblem.t ->
    (T2.Formula.t, T2.T.t, T2.Ty.t) NunFO.Problem.t
end

(** {2 Convert FO to HO} *)

module OfFO(T : S)(FO : NunFO.VIEW) : sig
  val convert_ty : FO.Ty.t -> T.ty
  val convert_term : FO.T.t -> T.t
  val convert_formula : FO.Formula.t -> T.t

  val convert_model : FO.term_or_form NunModel.t -> T.t NunModel.t
end

val to_fo :
  (module S with type t = 'a
    and type invariant_poly = NunMark.monomorph
    and type invariant_meta = NunMark.without_meta) ->
  (module NunFO.S with type T.t = 't and type formula = 'f and type Ty.t = 'ty) ->
  (('a, 'a, NunMark.linear) NunProblem.t,
    ('f, 't, 'ty) NunFO.Problem.t,
    ('t,'f) NunFO.term_or_form_view NunModel.t,
    'a NunModel.t
  ) NunTransform.t

val to_fo_no_model :
  (module S with type t = 'a
    and type invariant_poly = NunMark.monomorph
    and type invariant_meta = NunMark.without_meta) ->
  (module NunFO.S with type T.t = 't and type formula = 'f and type Ty.t = 'ty) ->
  (('a, 'a, NunMark.linear) NunProblem.t,
    ('f, 't, 'ty) NunFO.Problem.t,
    'b, 'b
  ) NunTransform.t

(** {2 Conversion} *)

module Convert(T1 : VIEW)(T2 : S
  with type invariant_poly=T1.invariant_poly
  and type invariant_meta=T1.invariant_meta
) : sig
  val convert : T1.t -> T2.t
end

(** {2 Conversion of UntypedAST to HO, without Type-Checking}

  This should be useful mostly for tests: parse and convert a term to a usable
  format in a simple way *)

module OfUntyped(T : S_POLY) : sig
  exception Error of NunUntypedAST.term * string

  val convert_term : NunUntypedAST.term -> T.t
end
