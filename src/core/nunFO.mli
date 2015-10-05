
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms and Formulas}

  This is the end of the chain, where formulas and terms are ready to be
  sent to some SMT solver. Types are monomorphic, formulas are first-order
*)

type id = NunID.t
type 'a var = 'a NunVar.t

module TyBuiltin : sig
  type t =
    | Prop
  val equal : t -> t -> bool
  val print : Format.formatter -> t -> unit
end

module Builtin : sig
  type t =
    | Int of int (* TODO use zarith *)
  val equal : t -> t -> bool
  val print : Format.formatter -> t -> unit
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | Let of 'ty var * 't * 't

(** Formula *)
type ('f, 't, 'ty) form_view =
  | Atom of 't
  | True
  | False
  | Eq of 't * 't
  | And of 'f list
  | Or of 'f list
  | Not of 'f
  | Imply of 'f * 'f
  | Equiv of 'f * 'f
  | Forall of 'ty var * 'f
  | Exists of 'ty var * 'f

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

(** {1 First-Order Formulas, Terms, Types} *)
module type S = sig
  module Ty : sig
    type t

    val view : t -> t ty_view

    type arrow = t list * t
    (** list of args, return *)

    val const : id -> t
    val app : id -> t list -> t
    val arrow : t list -> t -> arrow
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val var : Ty.t var -> t
  end

  module Formula : sig
    type t

    val view : t -> (t, T.t, Ty.t) form_view

    val atom : T.t -> t
    val true_ : t
    val false_ : t
    val eq : T.t -> T.t -> t
    val and_ : t list -> t
    val or_ : t list -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val equiv : t -> t -> t
    val forall : Ty.t var -> t -> t
    val exists : Ty.t var -> t -> t
  end
end

module Default : S

