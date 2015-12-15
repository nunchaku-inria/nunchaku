
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms and Formulas}

  This is the end of the chain, where formulas and terms are ready to be
  sent to some SMT solver. Types are monomorphic, formulas are first-order
*)

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

module TyBuiltin : sig
  type t =
    [ `Prop
    ]
  val equal : t -> t -> bool
  val print : Format.formatter -> t -> unit
end

module Builtin : sig
  type t =
    [ `Int of int (* TODO use zarith *)
    ]
  val equal : t -> t -> bool
  val print : Format.formatter -> t -> unit
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | DataTest of id * 't
  | DataSelect of id * int * 't
  | Undefined of id * 't (** ['t] is not defined here *)
  | Fun of 'ty var * 't  (** caution, not supported everywhere *)
  | Let of 'ty var * 't * 't
  | Ite of 't * 't * 't
  | True
  | False
  | Eq of 't * 't
  | And of 't list
  | Or of 't list
  | Not of 't
  | Imply of 't * 't
  | Equiv of 't * 't
  | Forall of 'ty var * 't
  | Exists of 'ty var * 't

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

(** Toplevel type: an arrow of atomic types *)
type 'ty toplevel_ty = 'ty list * 'ty

type 'ty constructor = {
  cstor_name: id;
  cstor_args: 'ty list; (* each arg: (selector, type) *)
}

type 'ty tydef = {
  ty_name: id;
  ty_cstors: 'ty constructor ID.Map.t;
}

type 'ty mutual_types = {
  tys_vars: id list;  (* type parameters *)
  tys_defs : 'ty tydef list;
}

(** Statement *)
type ('t, 'ty) statement =
  | TyDecl of id * int  (** number of arguments *)
  | Decl of id * 'ty toplevel_ty
  | Axiom of 't
  | MutualTypes of [`Data | `Codata] * 'ty mutual_types
  | Goal of 't

(** {2 Read-Only View} *)
module type VIEW = sig
  module Ty : sig
    type t
    type toplevel_ty = t list * t
    val view : t -> t ty_view
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)
  end
end

(** {2 View and Build Formulas, Terms, Types} *)
module type S = sig
  module Ty : sig
    type t
    type toplevel_ty = t list * t

    val view : t -> t ty_view

    val const : id -> t
    val app : id -> t list -> t
    val builtin : TyBuiltin.t -> t
    val arrow : t list -> t -> toplevel_ty
  end

  module T : sig
    type t
    val view : t -> (t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val data_test : id -> t -> t
    val data_select : id -> int -> t -> t
    val undefined : id -> t -> t
    val var : Ty.t var -> t
    val let_ : Ty.t var -> t -> t -> t
    val fun_ : Ty.t var -> t -> t
    val ite : t -> t -> t -> t
    val true_ : t
    val false_ : t
    val eq : t -> t -> t
    val and_ : t list -> t
    val or_ : t list -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val equiv : t -> t -> t
    val forall : Ty.t var -> t -> t
    val exists : Ty.t var -> t -> t
  end
end

type ('t, 'ty) repr =
  (module VIEW with type T.t = 't and type Ty.t = 'ty)

type ('t, 'ty) build =
  (module S with type T.t = 't and type Ty.t = 'ty)

module Default : S

val default_repr: (Default.T.t, Default.Ty.t) repr
val default: (Default.T.t, Default.Ty.t) build

(** {2 Problem} *)
module Problem : sig
  type ('t, 'ty) t = {
    statements: ('t, 'ty) statement CCVector.ro_vector;
  }

  val make : ('t, 'ty) statement CCVector.ro_vector -> ('t, 'ty) t
  val of_list : ('t, 'ty) statement list -> ('t, 'ty) t
  val statements : ('t, 'ty) t -> ('t, 'ty) statement CCVector.ro_vector
  val fold_flat_map :
    ('acc -> ('t, 'ty) statement -> 'acc * ('t2, 'ty2) statement list) ->
    'acc ->
    ('t, 'ty) t ->
    'acc * ('t2, 'ty2) t
end

(** {2 IO} *)

module type PRINT = sig
  module FO : VIEW

  val print_ty : FO.Ty.t printer
  val print_toplevel_ty : FO.Ty.toplevel_ty printer
  val print_term : FO.T.t printer
  val print_statement : (FO.T.t, FO.Ty.t) statement printer
  val print_model : (FO.T.t * FO.T.t) list printer
  val print_problem : (FO.T.t, FO.Ty.t) Problem.t printer
end

module Print(FO : VIEW) : PRINT with module FO = FO
