
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = NunID.t
type loc = NunLocation.t
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'ty, 'inv) def =
  | Fun_def of
      ('t, 'ty, 'inv) NunStatement.rec_defs *
      ('t, 'ty, 'inv) NunStatement.rec_def *
      loc option
      (** ID is a defined fun/predicate. *)

  | Fun_spec of
      (('t, 'ty) NunStatement.spec_defs * loc option) list

  | Data of
      [`Codata | `Data] *
      'ty NunStatement.mutual_types *
      'ty NunStatement.tydef
      (** ID is a (co)data *)

  | Cstor of
      [`Codata | `Data] *
      'ty NunStatement.mutual_types *
      'ty NunStatement.tydef *
      'ty NunStatement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | NoDef
      (** Undefined symbol *)

(** All information on a given symbol *)
type ('t, 'ty, 'inv) info = {
  ty: 'ty; (** type of symbol *)
  decl_kind: NunStatement.decl;
  loc: loc option;
  def: ('t, 'ty, 'inv) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty, 'inv) t = private {
  infos: ('t, 'ty, 'inv) info NunID.PerTbl.t;
}

exception InvalidDef of id * string

val pp_invalid_def_ : exn printer

val create: unit -> _ t
(** Create a new environment *)

val loc: _ info -> loc option
val def: ('t,'ty,'inv) info -> ('t,'ty,'inv) def
val ty: (_,'ty,_) info -> 'ty
val decl_kind: _ info -> NunStatement.decl

val declare:
  ?loc:loc ->
  kind:NunStatement.decl ->
  env:('t, 'ty, 'inv) t ->
  id ->
  'ty ->
  ('t, 'ty, 'inv) t
(** Declare a symbol's type (as undefined, for now) *)

val rec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty, 'inv) NunStatement.rec_defs ->
  ('t, 'ty, 'inv) t
(** Add a definition of functions/predicates. They must not be declared yet. *)

val declare_rec_funs:
  ?loc:loc ->
  env:('t, 'ty, <ty:'i;..> as 'inv) t ->
  ('t, 'ty, <ty:'i;..>) NunStatement.rec_defs ->
  ('t, 'ty, 'inv) t
(** Similar to {!rec_funs}, but only declares the functions, without adding
    their definition *)

val spec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty) NunStatement.spec_defs ->
  ('t, 'ty, 'inv) t
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  kind:[`Data | `Codata] ->
  'ty NunStatement.mutual_types ->
  ('t, 'ty, 'inv) t
(** Define a new set of mutually recursive (co)data types.
    Also defines their constructors.
    @raise InvalidDef if some type/constructor already defined/declared *)

val add_statement :
  env:('t,'ty,'inv) t ->
  ('t,'ty,'inv) NunStatement.t ->
  ('t,'ty,'inv) t
(** Add any statement *)

val find : env:('t, 'ty, 'inv) t -> id -> ('t, 'ty, 'inv) info option

val find_exn : env:('t, 'ty, 'inv) t -> id -> ('t, 'ty, 'inv) info
(** @raise Not_found if ID not defined *)

val find_ty_exn : env:('t, 'ty, _) t -> id -> 'ty
(** Find the type of a symbol
    @raise Not_found if the symbol is not declared *)

val find_ty : env:('t, 'ty, _) t -> id -> 'ty option
(** Safe version of {!find_ty_exn} *)

val mem : env:_ t -> id:id -> bool
(** @return true if the symbol is at least declared *)
