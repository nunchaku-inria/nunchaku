
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Top-Level Statements (with locations)} *)

module Metadata = ProblemMetadata

type loc = Location.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a to_sexp = 'a -> CCSexp.t
type 'a or_error = ('a, string) CCResult.t

(** {2 Features}

    Features exposed by the problem, as a record of individual features *)

module Features : sig
  type t

  type value =
    | Present
    | Absent
    | Mono
    | Poly
    | Eqn_single
    | Eqn_nested
    | Eqn_app

  (* the various kind of features *)
  type key =
    | Ty
    | Eqn
    | If_then_else
    | Ind_preds
    | Match
    | Data
    | Fun

  val empty : t
  (** For writing specifications *)

  val full : t
  (** Every feature is on *)

  val update : key -> value -> t -> t
  (** [update k v t] sets the key [k] to [v] in [t]. This is useful to
      specify how a specification changed *)

  val of_list : (key * value) list -> t

  val check : t -> spec:t -> bool
  (** [check t ~spec] returns [true] if all features required by [spec] are
      valid in [t] *)

  val print : t printer
end

(** {2 Problem: a Set of Statements + Signature} *)

type ('t, 'ty) t = private {
  statements : ('t, 'ty) Statement.t CCVector.ro_vector;
  metadata: Metadata.t;
  features: Features.t;
}

val make :
  features:Features.t ->
  meta:Metadata.t ->
  ('t, 'ty) Statement.t CCVector.ro_vector ->
  ('t, 'ty) t
(** Build a problem from statements *)

val of_list :
  features:Features.t ->
  meta:Metadata.t ->
  ('t, 'ty) Statement.t list ->
  ('t, 'ty) t

val statements : ('t, 'ty) t -> ('t, 'ty) Statement.t CCVector.ro_vector
val metadata : _ t -> Metadata.t
val features : _ t -> Features.t

val update_meta : ('t,'ty) t -> (Metadata.t -> Metadata.t) -> ('t,'ty) t

val add_sat_means_unknown : bool -> ('t,'ty) t -> ('t,'ty) t
val set_sat_means_unknown : ('t,'ty) t -> ('t,'ty) t
val add_unsat_means_unknown : bool -> ('t,'ty) t -> ('t,'ty) t
val set_unsat_means_unknown : ('t,'ty) t -> ('t,'ty) t

val check_features : (_, _) t -> spec:Features.t -> unit
(** [check_features pb ~spec] checks that the problem's features
    match the given spec *)

val map_features : f:(Features.t -> Features.t) -> ('t, 'ty) t -> ('t, 'ty) t
(** update the problem's features *)

val iter_statements:
  f:(('t, 'ty) Statement.t -> unit) ->
  ('t,'ty) t ->
  unit

val map_statements :
  ?features:(Features.t -> Features.t) ->
  f:(('t, 'ty) Statement.t -> ('t2,'ty2) Statement.t) ->
  ('t,'ty) t ->
  ('t2,'ty2) t

val fold_map_statements :
  ?features:(Features.t -> Features.t) ->
  f:('acc -> ('t, 'ty) Statement.t -> 'acc * ('t2,'ty2) Statement.t) ->
  x:'acc ->
  ('t,'ty) t ->
  'acc * ('t2,'ty2) t

val flat_map_statements :
  ?features:(Features.t -> Features.t) ->
  f:(('t, 'ty) Statement.t -> ('t2,'ty2) Statement.t list) ->
  ('t,'ty) t ->
  ('t2,'ty2) t
(** Map each statement to a list of statements, and flatten the result into
    a new problem *)

val map :
  ?features:(Features.t -> Features.t) ->
  term:('a -> 'b) ->
  ty:('tya -> 'tyb) ->
  ('a, 'tya) t ->
  ('b, 'tyb) t

val map_with :
  ?features:(Features.t -> Features.t) ->
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

  val print : (TermInner.prec -> 't printer) -> 'ty printer -> ('t,'ty) t printer

  val print_head : (_,_) t printer
  (** print result, not content (i.e. not the model *)

  val to_sexp : 't to_sexp -> 'ty to_sexp -> ('t,'ty) t to_sexp
end
