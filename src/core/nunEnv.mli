
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = NunID.t
type loc = NunLocation.t
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'ty, 'inv) fun_def =
  | Rec of
      ('t, 'ty, 'inv) NunStatement.rec_defs *
      ('t, 'ty, 'inv) NunStatement.rec_def *
      loc option
  | Spec of
      ('t, 'ty) NunStatement.spec_defs *
      loc option

type ('t, 'ty, 'inv) def =
  | Fun of ('t, 'ty, 'inv) fun_def list
      (** ID is a defined fun/predicate. Can be defined in several places *)

  | Data of [`Codata | `Data] * 'ty NunStatement.mutual_types * 'ty NunStatement.tydef
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
  infos: ('t, 'ty, 'inv) info NunID.Tbl.t;
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
  env:('t, 'ty, _) t ->
  id ->
  'ty ->
  unit
(** Declare a symbol's type (as undefined, for now) *)

val rec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty, 'inv) NunStatement.rec_defs ->
  unit
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val spec_funs:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  ('t, 'ty) NunStatement.spec_defs ->
  unit
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data:
  ?loc:loc ->
  env:('t, 'ty, 'inv) t ->
  kind:[`Data | `Codata] ->
  'ty NunStatement.mutual_types ->
  unit
(** Define a new set of mutually recursive (co)data types.
    Also defines their constructors.
    @raise InvalidDef if some type/constructor already defined/declared *)

val find : env:('t, 'ty, 'inv) t -> id:id -> ('t, 'ty, 'inv) info option

val find_exn : env:('t, 'ty, 'inv) t -> id:id -> ('t, 'ty, 'inv) info
(** @raise Not_found if ID not defined *)

val find_ty : env:('t, 'ty, _) t -> id:id -> 'ty
(** Find the type of a symbol
    @raise Not_found if the symbol is not declared *)

val mem : env:_ t -> id:id -> bool
(** @return true if the symbol is at least declared *)
