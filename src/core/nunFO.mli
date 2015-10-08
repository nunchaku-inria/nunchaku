
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms and Formulas}

  This is the end of the chain, where formulas and terms are ready to be
  sent to some SMT solver. Types are monomorphic, formulas are first-order
*)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a printer = Format.formatter -> 'a -> unit

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
type ('f, 't, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | Fun of 'ty var * 't  (** caution, not supported everywhere *)
  | Let of 'ty var * 't * 't
  | Ite of 'f * 't * 't

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
  | F_ite of 'f * 'f * 'f  (* if then else *)

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

(** Toplevel type: an arrow of atomic types *)
type 'ty toplevel_ty = 'ty list * 'ty

(* TODO: try to merge back with NunProblem? *)

(** Problem *)
type ('f, 't, 'ty) statement =
  | TyDecl of id * int  (** number of arguments *)
  | Decl of id * 'ty toplevel_ty
  | Def of id * 'ty toplevel_ty * 't
  | FormDef of id * 'f
  | Axiom of 'f
  | Goal of 'f

(** {2 Read-Only View} *)
module type VIEW = sig
  type formula

  module Ty : sig
    type t
    type toplevel_ty = t list * t
    val view : t -> t ty_view
  end

  module T : sig
    type t
    val view : t -> (formula, t, Ty.t) view
    (** Observe the structure of the term *)
  end

  module Formula : sig
    type t = formula
    val view : t -> (t, T.t, Ty.t) form_view
  end
end

(** {2 View and Build Formulas, Terms, Types} *)
module type S = sig
  type formula

  module Ty : sig
    type t
    type toplevel_ty = t list * t

    val view : t -> t ty_view

    val const : id -> t
    val app : id -> t list -> t
    val arrow : t list -> t -> toplevel_ty
  end

  module T : sig
    type t
    val view : t -> (formula, t, Ty.t) view
    (** Observe the structure of the term *)

    val builtin : Builtin.t -> t
    val const : id -> t
    val app : id -> t list -> t
    val var : Ty.t var -> t
    val let_ : Ty.t var -> t -> t -> t
    val fun_ : Ty.t var -> t -> t
    val ite : formula -> t -> t -> t
  end

  module Formula : sig
    type t = formula

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
    val f_ite : t -> t -> t -> t
  end
end

module Default : S

(** {2 Problem} *)
module Problem : sig
  type ('f, 't, 'ty) t = {
    statements: ('f, 't, 'ty) statement list;
  }

  val make : ('f, 't, 'ty) statement list -> ('f, 't, 'ty) t
  val statements : ('f, 't, 'ty) t -> ('f, 't, 'ty) statement list
end

(** {2 IO} *)

module type PRINT = sig
  module FO : VIEW

  val print_ty : FO.Ty.t printer
  val print_toplevel_ty : FO.Ty.toplevel_ty printer
  val print_term : FO.T.t printer
  val print_formula : FO.Formula.t printer
  val print_statement : (FO.Formula.t, FO.T.t, FO.Ty.t) statement printer
  val print_model : (FO.T.t * FO.T.t) list printer
  val print_problem : (FO.Formula.t, FO.T.t, FO.Ty.t) Problem.t printer
end

module Print(FO : VIEW) : PRINT with module FO = FO