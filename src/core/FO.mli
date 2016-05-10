
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms and Formulas}

  This is the end of the chain, where formulas and terms are ready to be
  sent to some SMT solver. Types are monomorphic, formulas are first-order
*)

module Metadata = ProblemMetadata
module Res = Problem.Res

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

module TyBuiltin : sig
  type t =
    [ `Prop
    | `Unitype
    ]
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

module Builtin : sig
  type t =
    [ `Int of int (* TODO use zarith *)
    ]
  val equal : t -> t -> bool
  val compare : t -> t -> int
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
  | Unparsable of 'ty (** could not parse term *)
  | Fun of 'ty var * 't  (** caution, not supported everywhere *)
  | Mu of 'ty var * 't   (** caution, not supported everywhere *)
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
  | CardBound of id * [`Max | `Min] * int (** cardinality bound *)
  | MutualTypes of [`Data | `Codata] * 'ty mutual_types
  | Goal of 't

(** {2 View and Build Formulas, Terms, Types} *)

module Ty : sig
  type t
  type toplevel_ty = t list * t

  val view : t -> t ty_view

  val const : id -> t
  val app : id -> t list -> t
  val builtin : TyBuiltin.t -> t
  val arrow : t list -> t -> toplevel_ty

  val is_prop : t -> bool

  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module T : sig
  type t
  val view : t -> (t, Ty.t) view
  (** Observe the structure of the term *)

  val compare : t -> t -> int
  (** Fast total ordering on values of type [t].
      {b NOT} structural comparison!
      There is no guarantee that two terms that are only structurally equal,
      but that have been built independently, will compare to 0 *)

  val builtin : Builtin.t -> t
  val const : id -> t
  val app : id -> t list -> t
  val data_test : id -> t -> t
  val data_select : id -> int -> t -> t
  val undefined : id -> t -> t
  val unparsable : Ty.t -> t
  val var : Ty.t var -> t
  val let_ : Ty.t var -> t -> t -> t
  val fun_ : Ty.t var -> t -> t
  val mu : Ty.t var -> t -> t
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

(** {2 Problem} *)
module Problem : sig
  type ('t, 'ty) t = {
    statements: ('t, 'ty) statement CCVector.ro_vector;
    meta: Metadata.t;
  }

  val make : meta:Metadata.t -> ('t, 'ty) statement CCVector.ro_vector -> ('t, 'ty) t
  val of_list : meta:Metadata.t -> ('t, 'ty) statement list -> ('t, 'ty) t
  val statements : ('t, 'ty) t -> ('t, 'ty) statement CCVector.ro_vector
  val meta : _ t -> Metadata.t
  val map :
    meta:Metadata.t ->
    (('t, 'ty) statement -> ('t2, 'ty2) statement) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t
  val flat_map :
    meta:Metadata.t ->
    (('t, 'ty) statement -> ('t2, 'ty2) statement list) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t
  val fold_flat_map :
    meta:Metadata.t ->
    ('acc -> ('t, 'ty) statement -> 'acc * ('t2, 'ty2) statement list) ->
    'acc ->
    ('t, 'ty) t ->
    'acc * ('t2, 'ty2) t
end

(** {2 Utils} *)
module Util : sig
  val dt_of_term :
    vars:Ty.t Var.t list ->
    T.t ->
    (T.t, Ty.t) Model.DT.t
  (** Convert a term into a decision tree, or emit a warning and
      return a trivial tree with "unparsable" inside *)

  val problem_kinds : (_,Ty.t) Problem.t -> Model.symbol_kind ID.Map.t
end

(** {2 IO} *)

val print_ty : Ty.t printer
val print_toplevel_ty : Ty.toplevel_ty printer
val print_term : T.t printer
val print_statement : (T.t, Ty.t) statement printer
val print_model : (T.t * T.t) list printer
val print_problem : (T.t, Ty.t) Problem.t printer

(** {2 Conversion} *)

(** Assume there are no types (other than `Unitype), no datatypes, no
    pattern match... *)
module To_tptp : sig
  exception Error of string

  val conv_form : T.t -> FO_tptp.form
  (** @raise Error if conversion failed *)

  val conv_statement : (T.t, Ty.t) statement -> FO_tptp.statement option
  (** convert the statement. Some statements will just disappear (mostly,
      declarations).
      @raise Error if conversion failed *)

  val conv_problem : (T.t, Ty.t) Problem.t -> FO_tptp.problem
end

module Of_tptp : sig
  val conv_ty : FO_tptp.ty -> Ty.t
  val conv_term : FO_tptp.term -> T.t
  val conv_form : FO_tptp.form -> T.t
end

val pipe_tptp :
  ((T.t, Ty.t) Problem.t, FO_tptp.problem,
    (FO_tptp.term, FO_tptp.ty) Res.t,
    (T.t, Ty.t) Res.t) Transform.t
