
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = NunID.t
type loc = NunLocation.t
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'ty) fun_def =
  | Rec of
      ('t, 'ty) NunStatement.rec_defs *
      ('t,'ty) NunStatement.rec_def *
      loc option
  | Spec of
      ('t, 'ty) NunStatement.spec_defs *
      loc option

type ('t, 'ty) def =
  | Fun of ('t, 'ty) fun_def list
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
type ('t, 'ty) info = {
  ty: 'ty; (** type of symbol *)
  decl_kind: NunStatement.decl;
  loc: loc option;
  def: ('t, 'ty) def;
}

(** Maps ID to their type and definitions *)
type ('t, 'ty) t = private {
  infos: ('t, 'ty) info NunID.Tbl.t;
}

exception InvalidDef of id * string

val pp_invalid_def_ : exn printer

val create: unit -> ('t, 'ty) t
(** Create a new environment *)

val loc: (_,_) info -> loc option
val def: ('t,'ty) info -> ('t,'ty) def
val ty: (_,'ty) info -> 'ty
val decl_kind: (_,_) info -> NunStatement.decl

val declare:
  ?loc:loc ->
  kind:NunStatement.decl ->
  env:('t, 'ty) t ->
  id ->
  'ty ->
  unit
(** Declare a symbol's type (as undefined, for now) *)

val rec_funs:
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) NunStatement.rec_defs ->
  unit
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val spec_funs:
  ?loc:loc ->
  env:('t, 'ty) t ->
  ('t, 'ty) NunStatement.spec_defs ->
  unit
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data:
  ?loc:loc ->
  env:('t, 'ty) t ->
  kind:[`Data | `Codata] ->
  'ty NunStatement.mutual_types ->
  unit
(** Define a new set of mutually recursive (co)data types.
    Also defines their constructors.
    @raise InvalidDef if some type/constructor already defined/declared *)

val find : env:('t, 'ty) t -> id:id -> ('t, 'ty) info option

val find_exn : env:('t, 'ty) t -> id:id -> ('t, 'ty) info
(** @raise Not_found if ID not defined *)

val find_ty : env:('t, 'ty) t -> id:id -> 'ty
(** Find the type of a symbol
    @raise Not_found if the symbol is not declared *)

val mem : env:(_,_) t -> id:id -> bool
(** @return true if the symbol is at least declared *)
