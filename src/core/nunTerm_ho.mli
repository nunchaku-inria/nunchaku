
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]

module Builtin : module type of NunTerm_typed.Builtin

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
  | TyBuiltin of NunType_intf.Builtin.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)

module type VIEW = sig
  type t

  type ty = private t

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
  val builtin : Builtin.t -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunType_intf.Builtin.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_var : ty var -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t

  type signature = t NunID.Map.t

  val ty : sigma:signature -> t -> Ty.t or_error
  (** Compute the type of the given term in the given signature *)

  exception Undefined of id

  val ty_exn : sigma:signature -> t -> Ty.t
  (** @raise Ty.Error in case of error at an application
      @raise Undefined in case some symbol is not defined *)
end

module Default : S
