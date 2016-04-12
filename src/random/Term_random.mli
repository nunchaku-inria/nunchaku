
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Generation of Random Terms} *)

open Nunchaku_core

type rstate = Random.State.t
type 'a rgen = rstate -> 'a

module T = TermInner.Default

type term = T.t
type ty = T.t

val print_term : T.t CCFormat.printer

(** Signature used to generate random terms *)
val base_sig : ty Signature.t

(** {2 Generators} *)

val ty : ty rgen
(** Random type from {!base_sig} *)

val of_ty : ty -> term rgen
(** Random value of this type. *)

val prop : term rgen
(** random property (type [prop]) *)

val random : term rgen
(** Random term of any type *)

val arbitrary : term QCheck.arbitrary

val arbitrary_ty : term QCheck.arbitrary

val arbitrary_prop : term QCheck.arbitrary

val generate : ?rand:rstate -> 'a rgen -> 'a

val generate_l : ?n:int -> ?rand:rstate -> 'a rgen -> 'a list

(**/**)
val print_rules : unit -> unit
(**/**)

