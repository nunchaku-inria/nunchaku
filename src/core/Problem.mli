
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

type metadata = ProblemMetadata.t

type loc = Location.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a to_sexp = 'a -> Sexp_lib.t
type 'a or_error = ('a, string) CCResult.t

(** {2 Problem: a Set of Statements + Signature} *)

type ('t, 'ty) t = private {
  statements : ('t, 'ty) Statement.t CCVector.ro_vector;
  metadata: metadata;
}

val make :
  meta:metadata ->
  ('t, 'ty) Statement.t CCVector.ro_vector ->
  ('t, 'ty) t
(** Build a problem from statements *)

val of_list :
  meta:metadata ->
  ('t, 'ty) Statement.t list ->
  ('t, 'ty) t

val statements : ('t, 'ty) t -> ('t, 'ty) Statement.t CCVector.ro_vector
val metadata : (_,_) t -> metadata

val update_meta : ('t,'ty) t -> (metadata -> metadata) -> ('t,'ty) t

val add_sat_means_unknown : bool -> ('t,'ty) t -> ('t,'ty) t
val set_sat_means_unknown : ('t,'ty) t -> ('t,'ty) t
val add_unsat_means_unknown : bool -> ('t,'ty) t -> ('t,'ty) t
val set_unsat_means_unknown : ('t,'ty) t -> ('t,'ty) t

val iter_statements:
  f:(('t, 'ty) Statement.t -> unit) ->
  ('t,'ty) t ->
  unit

val map_statements :
  f:(('t, 'ty) Statement.t -> ('t2,'ty2) Statement.t) ->
  ('t,'ty) t ->
  ('t2,'ty2) t

val fold_map_statements :
  f:('acc -> ('t, 'ty) Statement.t -> 'acc * ('t2,'ty2) Statement.t) ->
  x:'acc ->
  ('t,'ty) t ->
  'acc * ('t2,'ty2) t

val flat_map_statements :
  f:(('t, 'ty) Statement.t -> ('t2,'ty2) Statement.t list) ->
  ('t,'ty) t ->
  ('t2,'ty2) t
(** Map each statement to a list of statements, and flatten the result into
    a new problem *)

val map :
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya) t ->
  ('b, 'tyb) t

val map_with :
  ?before:(unit -> ('b, 'tyb) Statement.t list) ->
  ?after:(unit -> ('b, 'tyb) Statement.t list) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya) t -> ('b, 'tyb) t
(** [map_with ~add ~term ~ty pb] is similar to [map ~term ~ty pb], but after
    processing each statement [st], [after ()] and [before()] are called,
    and the statements they return
    are added respectively before or after the translation of [st]. *)

(** Printer for a problem *)
module Print(P1 : TermInner.PRINT)(P2:TermInner.PRINT) : sig
  val print : (P1.t, P2.t) t printer
end

(** {2 Convert the term representations} *)
module Convert(T1 : TermInner.REPR)(T2 : TermInner.BUILD) : sig
  type ('a, 'b, 'c) inv = <eqn:'a; ind_preds:'b; ty: 'c>

  val convert :
    (T1.t, T1.t) t ->
    (T2.t, T2.t) t

  val pipe :
    unit ->
    ((T1.t, T1.t) t,
     (T2.t, T2.t) t,
     'ret, 'ret) Transform.t
end

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

val env : ?init:('t,'ty) Env.t -> ('t, 'ty) t -> ('t,'ty) Env.t
(** Build an environment defining/declaring every symbol of the problem.
    @param init initial env, if any
    @raise IllFormed if some declarations/definitions do not agree *)

(** {2 Result} *)

module Res : sig
  type info = {
    backend: string; (* which solver returned this result? *)
    time: float; (* time it took *)
    message: string option; (* additional message *)
  }

  (* a single reason why "unknown" *)
  type unknown_info =
    | U_timeout of info
    | U_out_of_scope of info
    | U_incomplete of info
    | U_other of info * string

  type (+'t,+'ty) t =
    | Unsat of info
    | Sat of ('t,'ty) Model.t * info
    | Unknown of unknown_info list (* can cumulate several reasons *)
    | Error of exn * info

  val mk_info : ?message:string -> backend:string -> time:float -> unit -> info

  val map : term:('t1 -> 't2) -> ty:('ty1 -> 'ty2) -> ('t1,'ty1) t -> ('t2, 'ty2) t

  val map_m :
    f:(('t1,'ty1) Model.t -> ('t2,'ty2) Model.t) ->
    ('t1, 'ty1) t ->
    ('t2, 'ty2) t

  val print : (TermInner.prec -> 't printer) -> 'ty printer -> ('t,'ty) t printer

  val print_info : info printer

  val print_unknown_info : unknown_info printer

  val print_head : (_,_) t printer
  (** print result, not content (i.e. not the model *)

  val to_sexp : 't to_sexp -> 'ty to_sexp -> ('t,'ty) t to_sexp
end
