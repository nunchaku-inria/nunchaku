
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

type 'a or_error = [`Ok of 'a | `Error of string]
type var = NunVar.t
type loc = NunLocation.t
type sym = NunSymbol.t

exception ScopingError of string * string * loc option
(** Scoping error for the given variable *)

(** {2 Interface For Types} *)
module type TYPE = sig
  include NunType_intf.S

  val loc : t -> loc option

  val deref : t -> t option

  val bind : var:t -> t -> unit
  (** [bind ~var t] binds the variable [var] to [t].
      @raise Invalid_argument if [var] is not a variable or if [var]
        is already bound *)

  val sym : ?loc:loc -> sym -> t
  val var : ?loc:loc -> var -> t
  val app : ?loc:loc -> t -> t list -> t
  val arrow : ?loc:loc -> t -> t -> t
  val forall : ?loc:loc -> var -> t -> t
end

(** {2 Conversion of Types from the parse tree} *)

module ConvertType(Ty : TYPE) : sig
  type env

  val prop : Ty.t  (** Type of propositions *)

  val convert : env:env -> NunUntypedAST.ty -> Ty.t or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_exn : env:env -> NunUntypedAST.ty -> Ty.t
  (** @raise ScopingError if the type isn't well-scoped *)
end

exception TypeError of string * loc option
(** Raised when the input is ill-typed or could not be inferred *)

(** {2 Typed Term} *)
module type TERM = sig
  include NunTerm_intf.S

  module Ty : TYPE

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val sym : ?loc:loc -> ty:ty -> sym -> t
  val var : ?loc:loc -> ty:ty -> var -> t
  val app : ?loc:loc -> ty:ty -> t -> ty_arg:ty list -> t list -> t
  val fun_ : ?loc:loc -> ty:ty -> var -> ty_arg:ty -> t -> t
  val let_ : ?loc:loc -> var -> t -> t -> t
  val forall : ?loc:loc -> var -> ty_arg:ty -> t -> t
  val exists : ?loc:loc -> var -> ty_arg:ty -> t -> t
end

(** {2 Type Inference/Checking} *)

module ConvertTerm(Term : TERM) : sig
  type env

  val convert : env:env -> NunUntypedAST.term -> Term.t or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)
end
