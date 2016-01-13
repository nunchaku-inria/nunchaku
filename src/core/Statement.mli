(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-level statement} *)

type id = ID.t
type loc = Location.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

type decl =
  | Decl_type
  | Decl_fun
  | Decl_prop

type 'ty defined = {
  defined_head: id; (* symbol being defined *)
  defined_ty: 'ty; (* type of the head symbol *)
}

type ('t, 'ty, 'kind) equations =
  | Eqn_linear :
      ('ty var list (* universally quantified vars, also arguments to [f] *)
      * 't (* right-hand side of equation *)
      * 't list (* side conditions *)
      ) list
      -> ('t, 'ty, <eqn:[`Linear];..>) equations
  | Eqn_nested :
      ('ty var list (* universally quantified vars *)
      * 't list (* arguments (patterns) to the defined term *)
      * 't  (* right-hand side of equation *)
      * 't list (* additional conditions *)
      ) list
      -> ('t, 'ty, <eqn:[`Nested];..>) equations
  | Eqn_single :
      'ty var list (* function arguments *)
      *  't (* RHS *)
      -> ('t, 'ty, <eqn:[`Single];..>) equations

type ('t,'ty,'kind) rec_def = {
  rec_defined: 'ty defined;
  rec_kind: decl;
  rec_vars: 'ty var list; (* type variables in definitions *)
  rec_eqns: ('t, 'ty,'kind) equations; (* list of equations defining the term *)
}

type ('t, 'ty,'kind) rec_defs = ('t, 'ty,'kind) rec_def list

type ('t, 'ty) spec_defs = {
  spec_vars: 'ty var list; (* type variables used by defined terms *)
  spec_defined: 'ty defined list;  (* terms being specified together *)
  spec_axioms: 't list;  (* free-form axioms *)
}

(** A type constructor: name + type of arguments *)
type 'ty ty_constructor = {
  cstor_name: id; (** Name *)
  cstor_args: 'ty list; (** type arguments *)
  cstor_type: 'ty; (** type of the constructor (shortcut) *)
}

(** A (co)inductive type. The type variables [ty_vars] occur freely in
    the constructors' types. *)
type 'ty tydef = {
  ty_id : id;
  ty_vars : 'ty Var.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor ID.Map.t;
}

(** Mutual definitions of several types *)
type 'ty mutual_types = 'ty tydef list

(** Flavour of axiom *)
type ('t,'ty,'kind) axiom =
  | Axiom_std of 't list
    (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
    (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty,'kind) rec_defs
    (** Axioms are part of an admissible (partial) definition *)

type ('t, 'ty) pred_clause_cell = {
  clause_vars: 'ty var list; (* universally quantified vars *)
  clause_guard: 't option;
  clause_concl: 't;
}

type (_, _, _) pred_clause =
  | Pred_clause :
    ('t, 'ty) pred_clause_cell ->
    ('t, 'ty, <ind_preds:[`Present];..>) pred_clause

type ('t, 'ty, 'inv) pred_def = {
  pred_defined: 'ty defined;
  pred_tyvars: 'ty var list;
  pred_clauses: ('t, 'ty, 'inv) pred_clause list;
}

type ('t, 'ty) copy = {
  copy_id: ID.t; (* new name *)
  copy_vars: 'ty Var.t list; (* list of type variables *)
  copy_of: 'ty; (* [id vars] is a copy of [of_]. Set of variables = vars *)
  copy_abstract: ID.t; (* [of_ -> id vars] *)
  copy_concretize: ID.t; (* [id vars -> of] *)
  copy_pred: 't option; (* invariant *)
}

type ('term, 'ty, 'inv) view =
  | Decl of id * decl * 'ty
  | Axiom of ('term, 'ty, 'inv) axiom
  | TyDef of [`Data | `Codata] * 'ty mutual_types
  | Pred of [`Wf | `Not_wf] * [`Pred | `Copred] * ('term, 'ty, 'inv) pred_def list
  | Copy of ('term, 'ty) copy
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

type ('term, 'ty, 'inv) t = private {
  view: ('term, 'ty, 'inv) view;
  info: info;
}

type ('t, 'ty, 'inv) statement = ('t, 'ty, 'inv) t

val tydef_vars : 'ty tydef -> 'ty Var.t list
val tydef_id : _ tydef -> id
val tydef_type : 'ty tydef -> 'ty
val tydef_cstors : 'ty tydef -> 'ty ty_constructor ID.Map.t

val info_default : info

val view : ('term,'ty,'inv) t -> ('term, 'ty,'inv) view
val loc : _ t -> loc option
val name : _ t -> string option
val info : _ t -> info

val mk_decl : info:info  -> id -> decl -> 'ty -> ('t,'ty,'inv) t
val mk_axiom : info:info -> ('a,'ty,'inv) axiom -> ('a, 'ty,'inv) t
val mk_ty_def : info:info -> [`Data | `Codata] -> 'ty mutual_types -> (_, 'ty,_) t

val ty_decl : info:info -> id -> 'a -> (_, 'a, _) t
(** declare a type constructor *)

val decl : info:info -> id -> 'a -> (_, 'a, _) t
(** declare a function symbol *)

val prop_decl : info:info -> id -> 'a -> (_, 'a, _) t
(** Declare a proposition ([prop] must be provided) *)

val axiom : info:info -> 'a list -> ('a,_,_) t
(** Axioms without additional assumptions *)

val axiom1 : info:info -> 'a -> ('a,_,_) t

val axiom_spec : info:info -> ('a,'ty) spec_defs -> ('a,'ty,_) t
(** Axiom that can be ignored if not explicitely depended upon by the goal *)

val axiom_rec : info:info -> ('a,'ty,'inv) rec_defs -> ('a,'ty,'inv) t
(** Axiom that is part of an admissible (mutual, partial) definition. *)

val data : info:info -> 'ty mutual_types -> (_, 'ty, _) t

val codata : info:info -> 'ty mutual_types -> (_, 'ty, _) t

val pred : info:info -> wf:[`Wf | `Not_wf] ->
  ('t, 'ty, 'inv) pred_def list -> ('t, 'ty, 'inv) t

val copred : info:info -> wf:[`Wf | `Not_wf] ->
  ('t, 'ty, 'inv) pred_def list -> ('t, 'ty, 'inv) t

val mk_pred : info:info -> wf:[`Wf | `Not_wf] -> [`Pred | `Copred] ->
  ('t, 'ty, 'inv) pred_def list -> ('t, 'ty, 'inv) t

val copy : info:info -> ('t, 'ty) copy -> ('t, 'ty, 'inv) t

val goal : info:info -> 'a -> ('a,_,_) t
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
  abstract:ID.t ->
  concretize:ID.t ->
  vars:'ty Var.t list ->
  ID.t ->
  ('t, 'ty) copy

val find_rec_def : defs:('a, 'b, 'c) rec_def list -> ID.t -> ('a, 'b, 'c) rec_def option

val find_tydef : defs:'a tydef list -> ID.t -> 'a tydef option

val find_pred : defs:('a, 'b, 'inv) pred_def list -> ID.t -> ('a, 'b, 'inv) pred_def option

val map_defined:
  f:('ty -> 'ty2) ->
  'ty defined ->
  'ty2 defined

val map_eqns:
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty, <eqn:'inv;..>) equations ->
  ('t2, 'ty2, <eqn:'inv;..>) equations

val map_clause:
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty, <ind_preds:'inv;..>) pred_clause ->
  ('t2, 'ty2, <ind_preds:'inv;..>) pred_clause

val cast_eqns:
  ('t, 'ty, <eqn:'inv;..>) equations ->
  ('t, 'ty, <eqn:'inv;..>) equations
(** Useful to change the invariants that are not related to equations *)

val map_rec_def :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty, <eqn:'inv;..>) rec_def ->
  ('t2, 'ty2, <eqn:'inv;..>) rec_def

val cast_rec_def:
  ('t, 'ty, <eqn:'inv;..>) rec_def ->
  ('t, 'ty, <eqn:'inv;..>) rec_def

val map_rec_defs :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty, <eqn:'inv;..>) rec_defs ->
  ('t2, 'ty2, <eqn:'inv;..>) rec_defs

val cast_rec_defs:
  ('t, 'ty, <eqn:'inv;..>) rec_defs ->
  ('t, 'ty, <eqn:'inv;..>) rec_defs

val map_spec_defs :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty) spec_defs ->
  ('t2, 'ty2) spec_defs

val map_pred :
  term:('a -> 'a1) -> ty:('b -> 'b1) ->
  ('a,'b,<ind_preds:'inv;..>) pred_def  ->
  ('a1,'b1,<ind_preds:'inv;..>) pred_def

val map_preds :
  term:('a -> 'a1) -> ty:('b -> 'b1) ->
  ('a,'b,<ind_preds:'inv;..>) pred_def list ->
  ('a1,'b1,<ind_preds:'inv;..>) pred_def list

val map_copy :
  term:('t1 -> 't2) ->
  ty:('ty1 -> 'ty2) ->
  ('t1,'ty1) copy ->
  ('t2,'ty2) copy

val cast_pred :
  ('t, 'ty, <ind_preds:'inv;..>) pred_def ->
  ('t, 'ty, <ind_preds:'inv;..>) pred_def

val cast_preds :
  ('t, 'ty, <ind_preds:'inv;..>) pred_def list ->
  ('t, 'ty, <ind_preds:'inv;..>) pred_def list

val map :
  term:('t -> 't2) ->
  ty:('ty -> 'ty2) ->
  ('t, 'ty, <eqn:'inv;ind_preds:'inv2;..>) t ->
  ('t2, 'ty2, <eqn:'inv;ind_preds:'inv2;..>) t

val fold :
  term:('a -> 't -> 'a) ->
  ty:('a -> 'ty -> 'a) ->
  'a -> ('t, 'ty, 'inv) t -> 'a

(** {2 Print} *)

module Print(Pt : TermInner.PRINT)(Pty : TermInner.PRINT) : sig
  val print_spec_defs : (Pt.t, Pty.t) spec_defs printer
  val print_pred_def : (Pt.t, Pty.t, _) pred_def printer
  val print_pred_defs : (Pt.t, Pty.t, _) pred_def list printer
  val print_rec_def : (Pt.t, Pty.t, _) rec_def printer
  val print_rec_defs : (Pt.t, Pty.t, _) rec_def list printer
  val print_copy : (Pt.t, Pty.t) copy printer
  val print : (Pt.t, Pty.t, _) t printer
end

