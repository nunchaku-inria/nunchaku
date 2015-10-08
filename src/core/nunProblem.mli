
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type loc = NunLocation.t
type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Top-level statement} *)

module Statement : sig
  type ('term, 'ty) view =
    | TyDecl of id * 'ty (** uninterpreted type *)
    | Decl of id * 'ty (** uninterpreted symbol *)
    | Def of id * 'ty * 'term (** defined function symbol *)
    | PropDef of id * 'ty * 'term (** defined symbol of type Prop. The type is prop. *)
    | Axiom of 'term
    | Goal of 'term

  type ('term,'ty) t

  val view : ('term,'ty) t -> ('term, 'ty) view

  val loc : (_,_) t -> loc option

  val ty_decl : ?loc:loc -> id -> 'a -> (_, 'a) t
  val decl : ?loc:loc -> id -> 'a -> (_, 'a) t
  val def : ?loc:loc -> id -> ty:'ty -> 'a -> ('a, 'ty) t
  val prop_def : ?loc:loc -> id -> prop:'ty -> 'a -> ('a, 'ty) t
  val axiom : ?loc:loc -> 'a -> ('a,_) t
  val goal : ?loc:loc -> 'a -> ('a,_) t

  val map :
    term:('t -> 't2) ->
    ty:('ty -> 'ty2) ->
    ('t, 'ty) t ->
    ('t2, 'ty2) t

  (** {2 Print} *)

  val print : 'a printer -> 'b printer -> ('a,'b) t printer
  val print_list : 'a printer -> 'b printer -> ('a,'b) t list printer
end

(** {2 Signature} *)

module Signature : sig
  type 'ty t = 'ty NunID.Map.t

  val empty : _ t

  val mem : sigma:'a t -> id -> bool
  val find : sigma:'a t -> id -> 'a option
  val find_exn : sigma:'a t -> id -> 'a (** @raise Not_found *)

  val declare : sigma:'a t -> id -> 'a -> 'a t
end

(** {2 Problem: a Set of Statements + Signature} *)

type ('t, 'ty) t = private {
  statements : ('t, 'ty) Statement.t list;
}

val make :
  ('t, 'ty) Statement.t list ->
  ('t, 'ty) t
(** Build a problem from a list of statements *)

val statements : ('t, 'ty) t -> ('t, 'ty) Statement.t list

val map : term:('a -> 'b) -> ty:('tya -> 'tyb) -> ('a, 'tya) t -> ('b, 'tyb) t

val print : 'a printer -> 'b printer -> ('a,'b) t printer
(** Printer for a problem *)

exception IllFormed of string
(** Ill-formed problem *)

val goal : ('t, _) t -> 't
(** [goal pb] returns the unique goal of [pb], or fails. A problem that doesn't
    have a single goal is ill-formed
    @raise IllFormed if the problem doesn't have exactly one goal *)

val signature : ?init:'ty Signature.t -> (_, 'ty) t -> 'ty Signature.t
(** Gather the signature of every declared symbol
    @param init initial signature, if any
    @raise IllFormed if some symbol is declared twice *)

(** {2 Model} *)

module Model : sig
  type 't t = ('t * 't) list

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end
