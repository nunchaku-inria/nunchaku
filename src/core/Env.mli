
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = ID.t
type loc = Location.t
type 'a printer = Format.formatter -> 'a -> unit

type (+'t, +'ty) def =
  | Fun_def of
      ('t, 'ty) Statement.rec_defs *
      ('t, 'ty) Statement.rec_def *
      loc option
      (** ID is a defined fun/predicate. *)

  | Fun_spec of
      ('t, 'ty) Statement.spec_defs * loc option

  | Data of
      [`Codata | `Data] *
      'ty Statement.mutual_types *
      'ty Statement.tydef
      (** ID is a (co)data *)

  | Cstor of
      [`Codata | `Data] *
      'ty Statement.mutual_types *
      'ty Statement.tydef *
      'ty Statement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | Pred of
      [`Wf | `Not_wf] *
      [`Pred | `Copred] *
      ('t, 'ty) Statement.pred_def *
      ('t, 'ty) Statement.pred_def list *
      loc option

  | Copy_ty of ('t, 'ty) Statement.copy
    (** ID is the copy type *)

  | Copy_abstract of ('t, 'ty) Statement.copy
    (** ID is the abstraction function *)

  | Copy_concrete of ('t, 'ty) Statement.copy
    (** ID is the concretization function *)

  | NoDef
      (** Undefined symbol *)

(** All information on a given symbol *)
type (+'t, +'ty) info = {
  ty: 'ty; (** type of symbol *)
  decl_attrs: Statement.decl_attr list;
  loc: loc option;
  def: ('t, 'ty) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty) t = private {
  infos: ('t, 'ty) info ID.PerTbl.t;
}

exception InvalidDef of id * string

val pp_invalid_def_ : exn printer

val create: ?size:int -> unit -> (_,_) t
(** Create a new environment *)

val loc: (_,_) info -> loc option
val def: ('t,'ty) info -> ('t,'ty) def
val ty: (_,'ty) info -> 'ty

val is_fun : (_,_) info -> bool (** spec/rec *)
val is_rec : (_,_) info -> bool (** rec *)
val is_data : (_,_) info -> bool
val is_cstor : (_,_) info -> bool
val is_not_def : (_,_) info -> bool

val is_incomplete : (_,_) info -> bool
val is_abstract : (_,_) info -> bool

val declare:
  ?loc:loc ->
  attrs:Statement.decl_attr list ->
  env:('t, 'ty) t ->
  id ->
  'ty ->
  ('t, 'ty) t
(** Declare a symbol's type (as undefined, for now) *)

val rec_funs:
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) Statement.rec_defs ->
  ('t, 'ty) t
(** Add a definition of functions/predicates. They must not be declared yet. *)

val declare_rec_funs:
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) Statement.rec_defs ->
  ('t, 'ty) t
(** Similar to {!rec_funs}, but only declares the functions, without adding
    their definition *)

val spec_funs:
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) Statement.spec_defs ->
  ('t, 'ty) t
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data:
  ?loc:loc ->
  env:('t, 'ty) t ->
  kind:[`Data | `Codata] ->
  'ty Statement.mutual_types ->
  ('t, 'ty) t
(** Define a new set of mutually recursive (co)data types.
    Also defines their constructors.
    @raise InvalidDef if some type/constructor already defined/declared *)

val def_preds :
  ?loc:loc ->
  env:('t, 'ty) t ->
  wf:[`Wf | `Not_wf] ->
  kind:[`Pred | `Copred] ->
  ('t, 'ty) Statement.pred_def list ->
  ('t, 'ty) t

val add_copy :
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) Statement.copy ->
  ('t, 'ty) t

val add_statement : env:('t,'ty) t -> ('t,'ty) Statement.t -> ('t,'ty) t
(** Add any statement *)

val add_statement_l : env:('t,'ty) t -> ('t,'ty) Statement.t list -> ('t,'ty) t
(** Add any statements *)

val find : env:('t, 'ty) t -> id -> ('t, 'ty) info option

exception UndefinedID of ID.t

val find_exn : env:('t, 'ty) t -> id -> ('t, 'ty) info
(** @raise UndefinedID if ID not defined *)

val find_ty_exn : env:('t, 'ty) t -> id -> 'ty
(** Find the type of a symbol
    @raise UndefinedID if the symbol is not declared *)

val find_ty : env:('t, 'ty) t -> id -> 'ty option
(** Safe version of {!find_ty_exn} *)

module Util(T : TermInner.S) : sig
  type term = T.t
  type ty = T.t

  val ty : env:(term,ty) t -> term -> ty TermInner.or_error
  (** Compute type of this term *)

  val ty_exn : env:(term,ty) t -> term -> ty

  val info_of_ty : env:(term,ty) t -> ty -> (term, ty) info TermInner.or_error
  (** [info_of_ty ~env ty] finds the information related to the given
      type. *)

  exception No_head of ty

  val info_of_ty_exn : env:(term,ty) t -> ty -> (term, ty) info
  (** Unsafe version of {!info_of_ty}
      @raise No_head if the type is not an (applied) constant *)
end

val mem : env:(_,_) t -> id:id -> bool
(** @return true if the symbol is at least declared *)

module Print(Pt : TermInner.PRINT)(Pty : TermInner.PRINT) : sig
  val print : (Pt.t, Pty.t) t printer
end
