
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 First-Order Monomorphic Terms and Formulas}

    This is the end of the chain, where formulas and terms are ready to be
    sent to some SMT solver. Types are monomorphic, formulas are first-order
*)

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = ('a, string) CCResult.t
type metadata = ProblemMetadata.t
type ('a,'b) res = ('a,'b) Problem.Res.t

module TyBuiltin : sig
  type t =
    [ `Prop
    | `Unitype
    ]
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : t printer
end

module Builtin : sig
  type t =
    [ `Int of int (* TODO use zarith *)
    ]
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : t printer
end

(** Term *)
type ('t, 'ty) view =
  | Builtin of Builtin.t
  | Var of 'ty var
  | App of id * 't list
  | DataTest of id * 't
  | DataSelect of id * int * 't
  | Undefined of 't (** ['t] is not defined here *)
  | Undefined_atom of id * 'ty toplevel_ty * 't list (** some undefined term of given topleveltype, + args *)
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

(** Toplevel type: an arrow of atomic types *)
and 'ty toplevel_ty = 'ty list * 'ty

(** Type *)
type 'ty ty_view =
  | TyBuiltin of TyBuiltin.t
  | TyApp of id * 'ty list

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

type attr =
  | Attr_pseudo_prop
  | Attr_pseudo_true
  | Attr_card_hint of [`Max | `Min] * int (** cardinality bound hint *)

(** Statement *)
type ('t, 'ty) statement =
  | TyDecl of id * int * attr list (** number of arguments *)
  | Decl of id * 'ty toplevel_ty * attr list
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
  val hash : t -> int

  val to_seq : t -> t Sequence.t
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

  val equal : t -> t -> bool
  val hash : t -> int

  val builtin : Builtin.t -> t
  val const : id -> t
  val app : id -> t list -> t
  val data_test : id -> t -> t
  val data_select : id -> int -> t -> t
  val undefined : t -> t
  val undefined_atom : id -> Ty.toplevel_ty -> t list -> t
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

  val to_seq : t -> t Sequence.t
  (** subterms *)
end

(** {2 Problem} *)
module Problem : sig
  type ('t, 'ty) t = {
    statements: ('t, 'ty) statement CCVector.ro_vector;
    meta: metadata;
  }

  val make : meta:metadata -> ('t, 'ty) statement CCVector.ro_vector -> ('t, 'ty) t
  val of_list : meta:metadata -> ('t, 'ty) statement list -> ('t, 'ty) t
  val statements : ('t, 'ty) t -> ('t, 'ty) statement CCVector.ro_vector
  val meta : (_,_) t -> metadata
  val map :
    meta:metadata ->
    (('t, 'ty) statement -> ('t2, 'ty2) statement) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t
  val flat_map :
    meta:metadata ->
    (('t, 'ty) statement -> ('t2, 'ty2) statement list) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t
  val fold_flat_map :
    meta:metadata ->
    ('acc -> ('t, 'ty) statement -> 'acc * ('t2, 'ty2) statement list) ->
    'acc ->
    ('t, 'ty) t ->
    'acc * ('t2, 'ty2) t

  val to_seq : ('t,'ty) t -> ('t,'ty) statement Sequence.t
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

val tys_of_toplevel_ty : 'ty toplevel_ty -> 'ty Sequence.t
val terms_of_statement : ('t, _) statement -> 't Sequence.t
val tys_of_statement : (_, 'ty) statement -> 'ty Sequence.t

(** {2 IO} *)

val pp_ty : Ty.t printer
val pp_toplevel_ty : Ty.toplevel_ty printer
val pp_term : T.t printer
val pp_term' : _ -> T.t printer
val pp_statement : (T.t, Ty.t) statement printer
val pp_model : (T.t * T.t) list printer
val pp_problem : (T.t, Ty.t) Problem.t printer
