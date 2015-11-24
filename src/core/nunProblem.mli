
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level NunStatements (with locations)} *)

type loc = NunLocation.t
type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Problem: a Set of NunStatements + Signature} *)

type 'a vec_ro = ('a, CCVector.ro) CCVector.t

module Metadata : sig
  type t = private {
    incomplete: bool;
  }

  val default: t
  val set_incomplete: t -> t
  val add_incomplete: t -> bool -> t
end

type ('t, 'ty, 'inv) t = private {
  statements : ('t, 'ty, 'inv) NunStatement.t vec_ro;
  metadata: Metadata.t;
}

val make :
  meta:Metadata.t ->
  ('t, 'ty, 'inv) NunStatement.t vec_ro ->
  ('t, 'ty, 'inv) t
(** Build a problem from statements *)

val of_list :
  meta:Metadata.t ->
  ('t, 'ty, 'inv) NunStatement.t list ->
  ('t, 'ty, 'inv) t

val statements : ('t, 'ty, 'inv) t -> ('t, 'ty, 'inv) NunStatement.t vec_ro
val metadata : _ t -> Metadata.t

val map_statements :
  f:(('t, 'ty, 'inv) NunStatement.t -> ('t2,'ty2,'inv2) NunStatement.t) ->
  ('t,'ty,'inv) t ->
  ('t2,'ty2,'inv2) t

val fold_map_statements :
  f:('acc -> ('t, 'ty, 'inv) NunStatement.t -> 'acc * ('t2,'ty2,'inv2) NunStatement.t) ->
  x:'acc ->
  ('t,'ty,'inv) t ->
  'acc * ('t2,'ty2,'inv2) t

val flat_map_statements :
  f:(('t, 'ty,'inv) NunStatement.t -> ('t2,'ty2,'inv2) NunStatement.t list) ->
  ('t,'ty,'inv) t ->
  ('t2,'ty2, 'inv2) t
(** Map each statement to a list of statements, and flatten the result into
    a new problem *)

val map :
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya, <eqn:'inv;..>) t ->
  ('b, 'tyb, <eqn:'inv;..>) t

val map_with :
  ?before:(unit -> ('b, 'tyb, <eqn:'inv;..> as 'inv2) NunStatement.t list) ->
  ?after:(unit -> ('b, 'tyb, 'inv2) NunStatement.t list) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya, <eqn:'inv;..>) t -> ('b, 'tyb, 'inv2) t
(** [map_with ~add ~term ~ty pb] is similar to [map ~term ~ty pb], but after
    processing each statement [st], [after ()] and [before()] are called,
    and the statements they return
    are added respectively before or after the translation of [st]. *)

(** Printer for a problem *)
module Print(P1 : NunTermInner.PRINT)(P2:NunTermInner.PRINT) : sig
  val print : (P1.t, P2.t, _) t printer
end

exception IllFormed of string
(** Ill-formed problem *)

val goal : ('t, _, _) t -> 't
(** [goal pb] returns the unique goal of [pb], or fails. A problem that doesn't
    have a single goal is ill-formed
    @raise IllFormed if the problem doesn't have exactly one goal *)

val signature : ?init:'ty NunSignature.t -> (_, 'ty, _) t -> 'ty NunSignature.t
(** Gather the signature of every declared symbol
    @param init initial signature, if any
    @raise IllFormed if some symbol is declared twice *)

val env : ?init:('t,'ty, 'inv) NunEnv.t -> ('t, 'ty, 'inv) t -> ('t,'ty, 'inv) NunEnv.t
(** Build an environment defining/declaring every symbol of the problem.
    @param init initial env, if any
    @raise IllFormed if some declarations/definitions do not agree *)

(** {2 Result} *)

module Res : sig
  type 't t =
    | Unsat
    | Sat of 't NunModel.t
    | Timeout

  val map : f:('a -> 'b) -> 'a t -> 'b t

  val print : 't printer -> 't t printer
end

(** {2 Conversion} *)

module Convert(T1 : NunTermInner.REPR)(T2 : NunTermInner.BUILD) : sig
  val convert :
    (T1.t, T1.t, <eqn:'a; ..> as 'inv) t ->
    (T2.t, T2.t, 'inv) t

  val pipe : unit ->
    ( (T1.t, T1.t, <eqn:'a; ..> as 'inv) t,
      (T2.t, T2.t, 'inv) t,
      'b, 'b
    ) NunTransform.transformation
end
