
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type loc = Location.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Problem: a Set of Statements + Signature} *)

module Metadata : sig
  type t = private {
    incomplete: bool;
  }

  val default: t
  val set_incomplete: t -> t
  val add_incomplete: t -> bool -> t
end

type ('t, 'ty, 'inv) t = private {
  statements : ('t, 'ty, 'inv) Statement.t CCVector.ro_vector;
  metadata: Metadata.t;
}

val make :
  meta:Metadata.t ->
  ('t, 'ty, 'inv) Statement.t CCVector.ro_vector ->
  ('t, 'ty, 'inv) t
(** Build a problem from statements *)

val of_list :
  meta:Metadata.t ->
  ('t, 'ty, 'inv) Statement.t list ->
  ('t, 'ty, 'inv) t

val statements : ('t, 'ty, 'inv) t -> ('t, 'ty, 'inv) Statement.t CCVector.ro_vector
val metadata : _ t -> Metadata.t

val iter_statements:
  f:(('t, 'ty, 'inv) Statement.t -> unit) ->
  ('t,'ty,'inv) t ->
  unit

val map_statements :
  f:(('t, 'ty, 'inv) Statement.t -> ('t2,'ty2,'inv2) Statement.t) ->
  ('t,'ty,'inv) t ->
  ('t2,'ty2,'inv2) t

val fold_map_statements :
  f:('acc -> ('t, 'ty, 'inv) Statement.t -> 'acc * ('t2,'ty2,'inv2) Statement.t) ->
  x:'acc ->
  ('t,'ty,'inv) t ->
  'acc * ('t2,'ty2,'inv2) t

val flat_map_statements :
  f:(('t, 'ty,'inv) Statement.t -> ('t2,'ty2,'inv2) Statement.t list) ->
  ('t,'ty,'inv) t ->
  ('t2,'ty2, 'inv2) t
(** Map each statement to a list of statements, and flatten the result into
    a new problem *)

val map :
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya, <eqn:'inv;ind_preds:'inv2;..>) t ->
  ('b, 'tyb, <eqn:'inv;ind_preds:'inv2;..>) t

val map_with :
  ?before:(unit -> ('b, 'tyb, <eqn:'inv;ind_preds:'invp;..> as 'inv2) Statement.t list) ->
  ?after:(unit -> ('b, 'tyb, 'inv2) Statement.t list) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya, 'inv2) t -> ('b, 'tyb, 'inv2) t
(** [map_with ~add ~term ~ty pb] is similar to [map ~term ~ty pb], but after
    processing each statement [st], [after ()] and [before()] are called,
    and the statements they return
    are added respectively before or after the translation of [st]. *)

(** Printer for a problem *)
module Print(P1 : TermInner.PRINT)(P2:TermInner.PRINT) : sig
  val print : (P1.t, P2.t, _) t printer
end

exception IllFormed of string
(** Ill-formed problem *)

val goal : ('t, _, _) t -> 't
(** [goal pb] returns the unique goal of [pb], or fails. A problem that doesn't
    have a single goal is ill-formed
    @raise IllFormed if the problem doesn't have exactly one goal *)

val signature : ?init:'ty Signature.t -> (_, 'ty, _) t -> 'ty Signature.t
(** Gather the signature of every declared symbol
    @param init initial signature, if any
    @raise IllFormed if some symbol is declared twice *)

val env : ?init:('t,'ty, 'inv) Env.t -> ('t, 'ty, 'inv) t -> ('t,'ty, 'inv) Env.t
(** Build an environment defining/declaring every symbol of the problem.
    @param init initial env, if any
    @raise IllFormed if some declarations/definitions do not agree *)

(** {2 Result} *)

module Res : sig
  type 't t =
    | Unsat
    | Sat of 't Model.t
    | Timeout

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end
