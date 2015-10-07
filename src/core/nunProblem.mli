
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type loc = NunLocation.t
type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit

(** {2 Top-level statement} *)

module Statement : sig
  type ('term, 'ty) view =
    | TyDecl of id * 'ty (** uninterpreted type *)
    | Decl of id * 'ty (** uninterpreted symbol *)
    | Def of id * 'ty * 'term (** defined function symbol *)
    | PropDef of id * 'term (** defined symbol of type Prop *)
    | Axiom of 'term
    | Goal of 'term

  type ('term,'ty) t

  val view : ('term,'ty) t -> ('term, 'ty) view

  val loc : (_,_) t -> loc option

  val ty_decl : ?loc:loc -> id -> 'a -> (_, 'a) t
  val decl : ?loc:loc -> id -> 'a -> (_, 'a) t
  val def : ?loc:loc -> id -> ty:'ty -> 'a -> ('a, 'ty) t
  val prop_def : ?loc:loc -> id -> 'a -> ('a, 'ty) t
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

(** {2 Model} *)

module Model : sig
  type 't t = ('t * 't) list

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end
