
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

type ('a, 'ty) view =
  | Builtin of NunBuiltin.T.t (** built-in symbol *)
  | Const of id (** top-level symbol *)
  | Var of 'ty var (** bound variable *)
  | App of 'a * 'a list
  | Fun of 'ty var * 'a
  | Forall of 'ty var * 'a
  | Exists of 'ty var * 'a
  | Let of 'ty var * 'a * 'a
  | Ite of 'a * 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunBuiltin.Ty.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)

module type VIEW = sig
  type t
  type ty = t

  val view : t -> (t, ty) view
end

module type S = sig
  include VIEW

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty

    exception Error of string * t * t list
    (** Raised when a type application fails *)

    val apply : t -> t list -> t
    (** [apply t l] computes the type of [f args] where [f : t] and [args : l]
        @raise Error if the arguments do not match *)
  end

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val ite : t -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t

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

(** {2 Computing Types} *)

exception Undefined of id
(** When a symbol is not defined *)

module ComputeType(T : S) : sig
  type signature = T.ty NunProblem.Signature.t

  val compute_signature :
    ?init:signature ->
    (T.t, T.ty) NunProblem.Statement.t Sequence.t ->
    signature
  (** Signature from statements *)

  val ty : sigma:signature -> T.t -> T.ty or_error
  (** Compute the type of the given term in the given signature *)

  val ty_exn : sigma:signature -> T.t -> T.ty
  (** @raise Ty.Error in case of error at an application
      @raise Undefined in case some symbol is not defined *)
end

(** {2 Printing} *)

module type PRINT = sig
  type term
  type ty

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

(** {2 View as FO terms}

  The views can fail if the terms are actually not first order *)

module AsFO(T : VIEW) : sig
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

val as_fo :
  (module VIEW with type t = 'a) ->
  (module NunFO.VIEW with type T.t = 'a and type Ty.t = 'a and type formula = 'a)
