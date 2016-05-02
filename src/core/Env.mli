
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = ID.t
type loc = Location.t
type 'a printer = Format.formatter -> 'a -> unit

type (+'t, +'ty, 'inv) def =
  | Fun_def of
      ('t, 'ty, 'inv) Statement.rec_defs *
      ('t, 'ty, 'inv) Statement.rec_def *
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
      ('t, 'ty, 'inv) Statement.pred_def *
      ('t, 'ty, 'inv) Statement.pred_def list *
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
type (+'t, +'ty, 'inv) info = {
  ty: 'ty; (** type of symbol *)
  decl_attrs: Statement.decl_attr list;
  loc: loc option;
  def: ('t, 'ty, 'inv) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty, 'inv) t = private {
  infos: ('t, 'ty, 'inv) info ID.PerTbl.t;
}

exception InvalidDef of id * string

val pp_invalid_def_ : exn printer

val create: ?size:int -> unit -> _ t
(** Create a new environment *)

val loc: _ info -> loc option
val def: ('t,'ty,'inv) info -> ('t,'ty,'inv) def
val ty: (_,'ty,_) info -> 'ty

val is_fun : _ info -> bool (** spec/rec *)
val is_rec : _ info -> bool (** rec *)
val is_data : _ info -> bool
val is_cstor : _ info -> bool

val is_incomplete : _ info -> bool
val is_abstract : _ info -> bool

val declare:
  ?loc:loc ->
  attrs:Statement.decl_attr list ->
  env:('t, 'ty, 'inv) t ->
  id ->
  'ty ->
  ('t, 'ty, 'inv) t
(** Declare a symbol's type (as undefined, for now) *)

val rec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty, 'inv) Statement.rec_defs ->
  ('t, 'ty, 'inv) t
(** Add a definition of functions/predicates. They must not be declared yet. *)

val declare_rec_funs:
  ?loc:loc ->
  env:('t, 'ty, <ty:'i;..> as 'inv) t ->
  ('t, 'ty, <ty:'i;..>) Statement.rec_defs ->
  ('t, 'ty, 'inv) t
(** Similar to {!rec_funs}, but only declares the functions, without adding
    their definition *)

val spec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty) Statement.spec_defs ->
  ('t, 'ty, 'inv) t
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  kind:[`Data | `Codata] ->
  'ty Statement.mutual_types ->
  ('t, 'ty, 'inv) t
(** Define a new set of mutually recursive (co)data types.
    Also defines their constructors.
    @raise InvalidDef if some type/constructor already defined/declared *)

val def_preds :
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  wf:[`Wf | `Not_wf] ->
  kind:[`Pred | `Copred] ->
  ('t, 'ty, 'inv) Statement.pred_def list ->
  ('t, 'ty, 'inv) t

val add_copy :
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty) Statement.copy ->
  ('t, 'ty, 'inv) t

val add_statement :
  env:('t,'ty,'inv) t ->
  ('t,'ty,'inv) Statement.t ->
  ('t,'ty,'inv) t
(** Add any statement *)

val find : env:('t, 'ty, 'inv) t -> id -> ('t, 'ty, 'inv) info option

exception UndefinedID of ID.t

val find_exn : env:('t, 'ty, 'inv) t -> id -> ('t, 'ty, 'inv) info
(** @raise UndefinedID if ID not defined *)

val find_ty_exn : env:('t, 'ty, _) t -> id -> 'ty
(** Find the type of a symbol
    @raise UndefinedID if the symbol is not declared *)

val find_ty : env:('t, 'ty, _) t -> id -> 'ty option
(** Safe version of {!find_ty_exn} *)

val mem : env:_ t -> id:id -> bool
(** @return true if the symbol is at least declared *)

module Print(Pt : TermInner.PRINT)(Pty : TermInner.PRINT) : sig
  val print : (Pt.t, Pty.t, _) t printer
end
