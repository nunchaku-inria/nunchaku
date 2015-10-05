
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type loc = NunLocation.t
type id = NunID.t

type ('term, 'ty) view =
  | Decl of id * 'ty (** uninterpreted symbol *)
  | Def of id * 'ty * 'term (** defined symbol *)
  | Axiom of 'term

type ('term,'ty) t

val view : ('term,'ty) t -> ('term, 'ty) view

val loc : (_,_) t -> loc option

val decl : ?loc:loc -> id -> 'a -> (_, 'a) t
val def : ?loc:loc -> id -> ty:'ty -> 'a -> ('a, 'ty) t
val axiom : ?loc:loc -> 'a -> ('a,_) t

type 'a printer = Format.formatter -> 'a -> unit

val print : 'a printer -> 'b printer -> ('a,'b) t printer

val print_list : 'a printer -> 'b printer -> ('a,'b) t list printer
