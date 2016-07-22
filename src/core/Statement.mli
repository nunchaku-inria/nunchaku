(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-level statement} *)

type id = ID.t
type loc = Location.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

type 'ty defined = {
  defined_head: id; (* symbol being defined *)
  defined_ty: 'ty; (* type of the head symbol *)
}

type (+'t, +'ty) equations =
  | Eqn_nested of
      ('ty var list (* universally quantified vars *)
      * 't list (* arguments (patterns) to the defined term *)
      * 't  (* right-hand side of equation *)
      * 't list (* additional conditions *)
      ) list
  | Eqn_single of
      'ty var list (* function arguments *)
      *  't (* RHS *)
  | Eqn_app of
      ID.t list (* application symbols *)
      * 'ty var list (* quantified vars *)
      * 't (* LHS of equation *)
      * 't (* RHS of equation *)

type (+'t,+'ty) rec_def = {
  rec_defined: 'ty defined;
  rec_vars: 'ty var list; (* type variables in definitions *)
  rec_eqns: ('t, 'ty) equations; (* list of equations defining the term *)
}

type (+'t, +'ty) rec_defs = ('t, 'ty) rec_def list

type (+'t, +'ty) spec_defs = {
  spec_vars: 'ty var list; (* type variables used by defined terms *)
  spec_defined: 'ty defined list;  (* terms being specified together *)
  spec_axioms: 't list;  (* free-form axioms *)
}

(** A type constructor: name + type of arguments *)
type +'ty ty_constructor = {
  cstor_name: id; (** Name *)
  cstor_args: 'ty list; (** type arguments *)
  cstor_type: 'ty; (** type of the constructor (shortcut) *)
}

(** A (co)inductive type. The type variables [ty_vars] occur freely in
    the constructors' types. *)
type +'ty tydef = {
  ty_id : id;
  ty_vars : 'ty Var.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor ID.Map.t;
}

(** Mutual definitions of several types *)
type +'ty mutual_types = 'ty tydef list

(** Flavour of axiom *)
type (+'t,+'ty) axiom =
  | Axiom_std of 't list
    (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
    (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty) rec_defs
    (** Axioms are part of an admissible (partial) definition *)

type (+'t, +'ty) pred_clause = {
  clause_vars: 'ty var list; (* universally quantified vars *)
  clause_guard: 't option;
  clause_concl: 't;
}

type (+'t, +'ty) pred_def = {
  pred_defined: 'ty defined;
  pred_tyvars: 'ty var list;
  pred_clauses: ('t, 'ty) pred_clause list;
}

type (+'t, +'ty) copy = {
  copy_id: ID.t; (* new name *)
  copy_vars: 'ty Var.t list; (* list of type variables *)
  copy_ty: 'ty;  (* type of [copy_id], of the form [type -> type -> ... -> type] *)
  copy_of: 'ty; (* [id vars] is a copy of [of_]. Set of variables = vars *)
  copy_to: 'ty; (* [id vars] *)
  copy_abstract: ID.t; (* [of -> id vars] *)
  copy_abstract_ty: 'ty;
  copy_concrete: ID.t; (* [id vars -> of] *)
  copy_concrete_ty: 'ty;
  copy_pred: 't option; (* invariant (prop) *)
}

(** Attribute on declarations *)
type decl_attr =
  | Attr_card_max of int (** maximal cardinality of type *)
  | Attr_card_min of int (** minimal cardinality of type *)
  | Attr_card_hint of Cardinality.t (** hint on the card of a type *)
  | Attr_incomplete (** encoding of some type with some values removed *)
  | Attr_abstract (** encoding of some type where some values are conflated *)
  | Attr_infinite (** infinite uninterpreted type *)
  | Attr_finite_approx of ID.t (** finite approximation of an infinite type *)
  | Attr_infinite_upcast (** cast finite approx to infinite type *)
  | Attr_pseudo_prop (** encoding of [prop] *)
  | Attr_pseudo_true (** encoding of [true_ : pseudo_prop] *)
  | Attr_exn of exn (** open case *)

type (+'term, +'ty) view =
  | Decl of id * 'ty * decl_attr list
  | Axiom of ('term, 'ty) axiom
  | TyDef of [`Data | `Codata] * 'ty mutual_types
  | Pred of [`Wf | `Not_wf] * [`Pred | `Copred] * ('term, 'ty) pred_def list
  | Copy of ('term, 'ty) copy
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

type (+'term, +'ty) t = private {
  view: ('term, 'ty) view;
  info: info;
}

type (+'t, +'ty) statement = ('t, 'ty) t

val mk_defined : ID.t -> 'ty -> 'ty defined

val tydef_vars : 'ty tydef -> 'ty Var.t list
val tydef_id : _ tydef -> id
val tydef_type : 'ty tydef -> 'ty
val tydef_cstors : 'ty tydef -> 'ty ty_constructor ID.Map.t

val info_default : info
val info_of_loc : Location.t option -> info

val view : ('term,'ty) t -> ('term, 'ty) view
val loc : _ t -> loc option
val name : _ t -> string option
val info : _ t -> info

val mk_axiom : info:info -> ('a,'ty) axiom -> ('a, 'ty) t
val mk_ty_def : info:info -> [`Data | `Codata] -> 'ty mutual_types -> (_, 'ty) t

val decl : info:info -> attrs:decl_attr list -> id -> 'a -> (_, 'a) t
(** declare a type/function/predicate *)

val axiom : info:info -> 'a list -> ('a,_) t
(** Axioms without additional assumptions *)

val axiom1 : info:info -> 'a -> ('a,_) t

val axiom_spec : info:info -> ('a,'ty) spec_defs -> ('a,'ty) t
(** Axiom that can be ignored if not explicitely depended upon by the goal *)

val axiom_rec : info:info -> ('a,'ty) rec_defs -> ('a,'ty) t
(** Axiom that is part of an admissible (mutual, partial) definition. *)

val data : info:info -> 'ty mutual_types -> (_, 'ty) t

val codata : info:info -> 'ty mutual_types -> (_, 'ty) t

val pred : info:info -> wf:[`Wf | `Not_wf] ->
  ('t, 'ty) pred_def list -> ('t, 'ty) t

val copred : info:info -> wf:[`Wf | `Not_wf] ->
  ('t, 'ty) pred_def list -> ('t, 'ty) t

val mk_pred : info:info -> wf:[`Wf | `Not_wf] -> [`Pred | `Copred] ->
  ('t, 'ty) pred_def list -> ('t, 'ty) t

val copy : info:info -> ('t, 'ty) copy -> ('t, 'ty) t

val goal : info:info -> 'a -> ('a,_) t
(** The goal of the problem *)

val mk_mutual_ty:
  ID.t ->
  ty_vars:'ty Var.t list ->
  cstors:(ID.t * 'ty list * 'ty) list ->
  ty:'ty ->
  'ty tydef
(** Constructor for {!tydef} *)

val mk_copy :
  ?pred:'t ->
  of_:'ty ->
  to_:'ty ->
  ty:'ty ->
  abstract:(ID.t * 'ty) ->
  concrete:(ID.t * 'ty) ->
  vars:'ty Var.t list ->
  ID.t ->
  ('t, 'ty) copy
(** Invariants:
    [to_ = app id vars]
    [snd abstract = of_ -> to_]
    [snd concrete = to_ -> of_] *)

val find_rec_def : defs:('a, 'b) rec_def list -> ID.t -> ('a, 'b) rec_def option

val find_tydef : defs:'a tydef list -> ID.t -> 'a tydef option

val find_pred : defs:('a, 'b) pred_def list -> ID.t -> ('a, 'b) pred_def option

val map_defined:
  f:('ty -> 'ty2) ->
  'ty defined ->
  'ty2 defined

val map_eqns:
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) equations ->
  ('t2, 'ty2) equations

val map_eqns_bind :
  bind:('acc -> 'ty Var.t -> 'acc * 'ty1 Var.t) ->
  term:('acc -> 'term -> 'term1) ->
  'acc ->
  ('term,'ty) equations ->
  ('term1,'ty1) equations

val map_clause:
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) pred_clause ->
  ('t2, 'ty2) pred_clause

val map_clause_bind :
  bind:('acc -> 'ty Var.t -> 'acc * 'ty1 Var.t) ->
  term:('acc -> 'term -> 'term1) ->
  'acc ->
  ('term,'ty) pred_clause ->
  ('term1,'ty1) pred_clause

val map_rec_def :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) rec_def ->
  ('t2, 'ty2) rec_def

val map_rec_def_bind :
  bind:('a -> 'b Var.t -> 'a * 'c Var.t) ->
  term:('a -> 'd -> 'e) ->
  ty:('a -> 'b -> 'c) ->
  'a ->
  ('d, 'b) rec_def ->
  ('e, 'c) rec_def

val map_rec_defs :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) rec_defs ->
  ('t2, 'ty2) rec_defs

val map_ty_def :
  ty:('ty -> 'ty2) ->
  'ty tydef ->
  'ty2 tydef

val map_ty_defs :
  ty:('ty -> 'ty2) ->
  'ty mutual_types ->
  'ty2 mutual_types

val map_spec_defs :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) spec_defs ->
  ('t2, 'ty2) spec_defs

val map_spec_defs_bind :
  bind:('b_acc -> 'ty Var.t -> 'b_acc * 'ty2 Var.t) ->
  term:('b_acc -> 't -> 't2) ->
  ty:('b_acc -> 'ty -> 'ty2) ->
  'b_acc ->
  ('t, 'ty) spec_defs ->
  ('t2, 'ty2) spec_defs

val map_pred :
  term:('a -> 'a1) -> ty:('b -> 'b1) ->
  ('a,'b) pred_def  ->
  ('a1,'b1) pred_def

val map_pred_bind :
  bind:('acc -> 'ty Var.t -> 'acc * 'ty2 Var.t) ->
  term:('acc -> 'term -> 'term2) ->
  ty:('acc -> 'ty -> 'ty2) ->
  'acc ->
  ('term, 'ty) pred_def ->
  ('term2, 'ty2) pred_def

val map_preds :
  term:('a -> 'a1) -> ty:('b -> 'b1) ->
  ('a,'b) pred_def list ->
  ('a1,'b1) pred_def list

val map_copy :
  term:('t1 -> 't2) ->
  ty:('ty1 -> 'ty2) ->
  ('t1,'ty1) copy ->
  ('t2,'ty2) copy

val map :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) t ->
  ('t2, 'ty2) t

val map_bind :
  bind:('b_acc -> 'ty Var.t -> 'b_acc * 'ty2 Var.t) ->
  term:('b_acc -> 't -> 't2) ->
  ty:('b_acc -> 'ty -> 'ty2) ->
  'b_acc ->
  ('t, 'ty) t ->
  ('t2, 'ty2) t
(** Similar to {!map}, but accumulating some value of type [b_acc] when
    entering binders *)

val fold_bind :
  bind:('b_acc -> 'ty Var.t -> 'b_acc) ->
  term:('b_acc -> 'a -> 't -> 'a) ->
  ty:('b_acc -> 'a -> 'ty -> 'a) ->
  'b_acc -> 'a -> ('t, 'ty) t -> 'a

val fold :
  term:('a -> 't -> 'a) ->
  ty:('a -> 'ty -> 'a) ->
  'a -> ('t, 'ty) t -> 'a

val iter :
  term:('t -> unit) ->
  ty:('ty -> unit) ->
  ('t, 'ty) t -> unit

val id_of_defined : _ defined -> ID.t
val ty_of_defined : 'ty defined -> 'ty
val defined_of_rec : (_, 'ty) rec_def -> 'ty defined
val defined_of_recs : (_, 'ty) rec_defs -> 'ty defined Sequence.t
val defined_of_spec : (_, 'ty) spec_defs -> 'ty defined Sequence.t
val defined_of_pred : (_, 'ty) pred_def -> 'ty defined
val defined_of_preds : (_, 'ty) pred_def list -> 'ty defined Sequence.t
val defined_of_cstor : 'ty ty_constructor -> 'ty defined
val defined_of_data : 'ty tydef -> 'ty defined Sequence.t
val defined_of_datas : 'ty mutual_types -> 'ty defined Sequence.t
val defined_of_copy : (_, 'ty) copy -> 'ty defined Sequence.t

val ids_of_copy : (_,_) copy -> ID.t Sequence.t

(** {2 Print} *)

val print_attr : decl_attr printer
val print_attrs : decl_attr list printer

module Print(Pt : TermInner.PRINT)(Pty : TermInner.PRINT) : sig
  val print_spec_defs : (Pt.t, Pty.t) spec_defs printer
  val print_clause : (Pt.t, Pty.t) pred_clause printer
  val print_clauses : (Pt.t, Pty.t) pred_clause list printer
  val print_pred_def : (Pt.t, Pty.t) pred_def printer
  val print_pred_defs : (Pt.t, Pty.t) pred_def list printer
  val print_eqns : ID.t -> (Pt.t, Pty.t) equations printer
  val print_rec_def : (Pt.t, Pty.t) rec_def printer
  val print_rec_defs : (Pt.t, Pty.t) rec_def list printer
  val print_tydef : Pty.t tydef printer
  val print_tydefs : ([`Data | `Codata] * Pty.t tydef list) printer
  val print_copy : (Pt.t, Pty.t) copy printer
  val print : (Pt.t, Pty.t) t printer
end

