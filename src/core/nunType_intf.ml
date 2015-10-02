
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type var = NunVar.t

module Builtin : sig
  type t =
    | Prop
  val equal : t -> t -> bool
  val to_string : t -> string
end = struct
  type t =
    | Prop
  let equal = (==)
  let to_string = function
    | Prop -> "prop"
end

type 'a view =
  | Kind (** the "type" of [Type], in some sense *)
  | Type (** the type of types *)
  | Builtin of Builtin.t (** Builtin type *)
  | Var of var
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of var * 'a  (** Polymorphic type *)

(** {2 Basic Interface: view, build} *)
module type S = sig
  type t

  val view : t -> t view

  val build : t view -> t

  val fold : ('a view -> 'a) -> t -> 'a
end

module type AS_TERM = sig
  type term
  type t = private term

  val is_Type : t -> bool (** type == Type? *)
  val is_Kind : t -> bool (** type == Kind? *)

  val to_term : t -> term
  val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  val of_term : term -> t option
  val of_term_exn : term -> t  (** @raise Failure if it is not a term *)
end

(** {2 Types with bindings, for unification} *)
module type UNIFIABLE = sig
  include S

  val deref : t -> t option

  val bind : var:t -> t -> unit
  (** [bind ~var t] binds the variable [var] to [t].
      @raise Invalid_argument if [var] is not a variable or if [var]
        is already bound *)

  include NunIntf.PRINT with type t := t
  (** Need to be able to print types *)
end
