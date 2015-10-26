
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

type ('t, 'ty) t = private {
  statements : ('t, 'ty) NunStatement.t vec_ro;
  metadata: Metadata.t;
}

val make : meta:Metadata.t -> ('t, 'ty) NunStatement.t vec_ro -> ('t, 'ty) t
(** Build a problem from statements *)

val of_list : meta:Metadata.t -> ('t, 'ty) NunStatement.t list -> ('t, 'ty) t

val statements : ('t, 'ty) t -> ('t, 'ty) NunStatement.t vec_ro
val metadata : (_,_) t -> Metadata.t

val map_statements :
  f:(('t, 'ty) NunStatement.t -> ('t2,'ty2) NunStatement.t) -> ('t,'ty) t -> ('t2,'ty2) t

val map : term:('a -> 'b) -> ty:('tya -> 'tyb) -> ('a, 'tya) t -> ('b, 'tyb) t

val map_with :
  ?before:(unit -> ('b, 'tyb) NunStatement.t list) ->
  ?after:(unit -> ('b, 'tyb) NunStatement.t list) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya) t -> ('b, 'tyb) t
(** [map_with ~add ~term ~ty pb] is similar to [map ~term ~ty pb], but after
    processing each statement [st], [after ()] and [before()] are called,
    and the statements they return
    are added respectively before or after the translation of [st]. *)

val print : ?pty_in_app:'b printer -> 'a printer -> 'b printer -> ('a,'b) t printer
(** Printer for a problem *)

exception IllFormed of string
(** Ill-formed problem *)

val goal : ('t, _) t -> 't
(** [goal pb] returns the unique goal of [pb], or fails. A problem that doesn't
    have a single goal is ill-formed
    @raise IllFormed if the problem doesn't have exactly one goal *)

val signature : ?init:'ty NunSignature.t -> (_, 'ty) t -> 'ty NunSignature.t
(** Gather the signature of every declared symbol
    @param init initial signature, if any
    @raise IllFormed if some symbol is declared twice *)

val env : ?init:('t,'ty) NunEnv.t -> ('t, 'ty) t -> ('t,'ty) NunEnv.t
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
