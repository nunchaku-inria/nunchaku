
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

module type VIEW = sig
  include NunTerm_intf.VIEW

  module Ty : sig
    type t = ty
    val view : t -> t NunType_intf.view
  end
end

module type S = sig
  include NunTerm_intf.VIEW

  module Ty : NunType_intf.AS_TERM with type term = t and type t = ty

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val app_builtin : NunBuiltin.T.t -> t list -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val ite : t -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t
  val eq : t -> t -> t

  val mk_bind : NunTerm_intf.binder -> Ty.t var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_kind : Ty.t (** Type of ty_type *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_var : ty var -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t
end

module Default : S

val default : (module S with type t = Default.t)

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
      @raise Error if the arguments do not match *)

  val ty_apply_full : T.ty -> T.t list -> T.ty * subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise Error if the arguments do not match *)

  type signature = T.ty NunProblem.Signature.t

  val ty : sigma:signature -> T.t -> T.ty or_error
  (** Compute the type of the given term in the given signature *)

  val ty_exn : sigma:signature -> T.t -> T.ty
  (** @raise Ty.Error in case of error at an application
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

(** {2 View as FO terms}

  The views can fail if the terms are actually not first order *)

module AsFO(T : S) : sig
  exception NotInFO of string * T.t
  (** Raised if a term is not in the first-order fragment *)

  (** Convert a problem in a "cheap" way (without allocating new terms) *)
  val convert_problem :
    (T.t, T.ty) NunProblem.t ->
    (T.t, T.t, T.ty) NunFO.Problem.t

  include NunFO.VIEW with type T.t = T.t
    and type Ty.t = T.ty
    and type formula = T.t
end

(** {2 Convert FO to HO} *)

module OfFO(T : S)(FO : NunFO.VIEW) : sig
  val convert_ty : FO.Ty.t -> T.ty
  val convert_term : FO.T.t -> T.t
  val convert_formula : FO.Formula.t -> T.t

  val convert_model : FO.term_or_form NunProblem.Model.t -> T.t NunProblem.Model.t
end

val to_fo :
  (module S with type t = 'a) ->
  (module NunFO.S with type T.t = 't and type formula = 'f) ->
  (('a, 'a) NunProblem.t,
    ('a, 'c, 'a) NunFO.Problem.t,
    ('t,'f) NunFO.term_or_form_view NunProblem.Model.t, 'a NunProblem.Model.t
  ) NunTransform.t

(** {2 Conversion} *)

module Convert(T1 : VIEW)(T2 : S) : sig
  val convert : T1.t -> T2.t
end

(** {2 Conversion of UntypedAST to HO, without Type-Checking}

  This should be useful mostly for tests: parse and convert a term to a usable
  format in a simple way *)

module OfUntyped(T : S) : sig
  exception Error of NunUntypedAST.term * string

  val convert_term : NunUntypedAST.term -> T.t
end
