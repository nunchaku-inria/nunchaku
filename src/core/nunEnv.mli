
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment}

  Maps (co)inductive types to their definition, functions
  to their specifications/axioms/recursive specifications,
  constructors to their types, and any symbol to its type *)

type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit

type ('t, 'ty) def =
  | Fun of ('t, 'ty) NunStatement.mutual_cases list
      (** ID is a defined fun/predicate. Can be defined in several places *)

  | Data of [`Codata | `Data] * 'ty NunStatement.mutual_types * 'ty NunStatement.tydef
      (** ID is a (co)data *)

  | Cstor of 'ty NunStatement.tydef * 'ty NunStatement.ty_constructor
      (** ID is a constructor (of the given type) *)

  | NoDef
      (** Undefined symbol *)

(** All information on a given symbol *)
type ('t, 'ty) info = {
  ty: 'ty; (** type of symbol *)
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

val declare : env:('t, 'ty) t -> id:id -> ty:'ty -> unit
(** Declare a symbol's type (as undefined, for now) *)

val def_funs : env:('t, 'ty) t -> ('t, 'ty) NunStatement.mutual_cases -> unit
(** Add a definition of functions/predicates. They can be already
    defined (or declared). *)

val def_data :
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
