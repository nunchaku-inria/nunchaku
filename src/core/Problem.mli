
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

module Metadata = ProblemMetadata

type loc = Location.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

(** {2 Problem: a Set of Statements + Signature} *)

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
val update_meta : ('t,'ty,'inv) t -> (Metadata.t -> Metadata.t) -> ('t,'ty,'inv) t

val add_sat_means_unknown : bool -> ('t,'ty,'inv) t -> ('t,'ty,'inv) t
val set_sat_means_unknown : ('t,'ty,'inv) t -> ('t,'ty,'inv) t
val add_unsat_means_unknown : bool -> ('t,'ty,'inv) t -> ('t,'ty,'inv) t
val set_unsat_means_unknown : ('t,'ty,'inv) t -> ('t,'ty,'inv) t

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
  ('a, 'tya, <eqn:'inv;ind_preds:'inv2;ty:'inv3;..>) t ->
  ('b, 'tyb, <eqn:'inv;ind_preds:'inv2;ty:'inv3;..>) t

val map_with :
  ?before:(unit -> ('b, 'tyb, <eqn:'inv;ind_preds:'invp;ty:_; ..> as 'inv2) Statement.t list) ->
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

(** {2 Convert the term representations} *)
module Convert(T1 : TermInner.REPR)(T2 : TermInner.BUILD) : sig
  type ('a, 'b, 'c) inv = <eqn:'a; ind_preds:'b; ty: 'c>

  val convert :
    (T1.t, T1.t, ('a,'b, 'c) inv) t ->
    (T2.t, T2.t, ('a,'b, 'c) inv) t

  val pipe :
    unit ->
    ((T1.t, T1.t, ('a, 'b, 'c) inv) t,
     (T2.t, T2.t, ('a, 'b, 'c) inv) t,
     'ret, 'ret) Transform.t
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
  type (+'t,+'ty) t =
    | Unsat
    | Sat of ('t,'ty) Model.t
    | Unknown
    | Timeout
    | Error of exn

  val map : term:('t1 -> 't2) -> ty:('ty1 -> 'ty2) -> ('t1,'ty1) t -> ('t2, 'ty2) t

  val map_m :
    f:(('t1,'ty1) Model.t -> ('t2,'ty2) Model.t) ->
    ('t1, 'ty1) t ->
    ('t2, 'ty2) t

  val print : 't printer -> 'ty printer -> ('t,'ty) t printer
end
