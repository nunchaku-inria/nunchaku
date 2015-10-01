
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type var = NunVar.t
type symbol = NunSymbol.t

type 'a view =
  | Sym of symbol (** Builtin type *)
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
