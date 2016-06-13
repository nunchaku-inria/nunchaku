
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a printer = 'a CCFormat.printer

(** {2 Features}

    Set of features that characterize a logic,
    as a record of individual features *)

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
    | Fun (* lambdas *)
    | HOF (* any higher-order fun *)
    | Copy

  val empty : t
  (** For writing specifications *)

  val full : t
  (** Every feature is on *)

  val update : key -> value -> t -> t
  (** [update k v t] sets the key [k] to [v] in [t]. This is useful to
      specify how a specification changed *)

  val update_l : (key * value) list -> t -> t

  val of_list : (key * value) list -> t

  val check : t -> spec:t -> bool
  (** [check t ~spec] returns [true] if all features required by [spec] are
      valid in [t] *)

  val print : t printer
end

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b], with reverse transformation from ['c]
    to ['d]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to perform the reverse
    transformation. *)
type ('a, 'b, 'c, 'd) t = Ex : ('a, 'b, 'c, 'd, 'st) inner -> ('a, 'b, 'c, 'd) t

(** Transformation with explicit hidden state *)
and ('a, 'b, 'c, 'd, 'st) inner = {
  name : string; (** name for the transformation, used for debug, CLI options, etc. *)
  encode : 'a -> ('b * 'st);
  decode : 'st -> 'c -> 'd;
  input_spec : Features.t;
  map_spec : Features.t -> Features.t;
  mutable on_input : ('a -> unit) list;
  mutable on_encoded : ('b -> unit) list;
  mutable on_decoded : ('d -> unit) list;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b, 'c, 'd) transformation = ('a, 'b, 'c, 'd) t
(** Alias to {!t} *)

val make :
  ?print:(Format.formatter -> 'st -> unit) ->
  ?on_input:('a -> unit) list ->
  ?on_encoded:('b -> unit) list ->
  ?on_decoded:('d -> unit) list ->
  ?input_spec:Features.t ->
  ?map_spec:(Features.t -> Features.t) ->
  name:string ->
  encode:('a -> ('b * 'st)) ->
  decode:('st -> 'c -> 'd) ->
  unit ->
  ('a, 'b, 'c, 'd) t
(** Constructor *)

val backward :
  name:string ->
  ('b -> 'c) ->
  ('a, 'a, 'b, 'c) t
(** [backward f] is the identity in the direct way, and the same as [f]
    in the way back *)

val nop : unit -> ('a, 'a, 'b, 'b) t
(** Transformation that does nothing *)

val on_encoded : (_, 'b, _, _) t -> f:('b -> unit) -> unit
(** [on_encoded tr ~f] registers [f] to be called on every value
    obtained by encoding through [tr] *)

val on_input : ('a, _, _, _) t -> f:('a -> unit) -> unit

(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe : sig
  (** Composite transformation from ['a] to ['b], with a reverse transformation
      from ['c] to ['d] *)
  type ('a, 'b, 'c, 'd) t = private
    | Id : ('a, 'a, 'c, 'c) t (** no transformation *)
    | Fail : ('a, 'b, 'c, 'd) t (** yields empty list *)
    | Flatten :
        ('a, 'b list, 'c, 'd) t ->
        ('a, 'b, 'c, 'd) t
    | Close :
        ('b1 -> ('c1 -> 'd) -> 'b2 * ('c2 -> 'd)) *
        ('a, 'b1, 'c1, 'd) t ->
        ('a, 'b2, 'c2, 'd) t
    | Comp :
        ('a, 'b, 'e, 'f) transformation *
        ('b, 'c, 'd, 'e) t ->
        ('a, 'c, 'd, 'f) t
    | Fork :
        ('a, 'b, 'c, 'd) t *
        ('a, 'b, 'c, 'd) t ->
        ('a, 'b, 'c, 'd) t

  (** Every constructor from here is "smart":
      - Fail is right-absorbing (e.g. [compose f fail = fail])
      - Fork with Id in both branches becomes the Id
      - Fork with Fail in a branch becomes the other branch *)

  val id : ('a, 'a, 'c, 'c) t

  val fail : ('a, 'b, 'c, 'd) t

  val flatten :
    ('a, 'b list, 'c, 'd) t ->
    ('a, 'b, 'c, 'd) t

  val close :
    f:('b1 -> ('c1 -> 'd) -> 'b2 * ('c2 -> 'd)) ->
    ('a, 'b1, 'c1, 'd) t ->
    ('a, 'b2, 'c2, 'd) t

  val compose :
    ('a, 'b, 'd1, 'e) transformation ->
    ('b, 'b2, 'c, 'd1) t -> ('a, 'b2, 'c, 'e) t

  val (@@@) :
    ('a, 'b, 'd1, 'e) transformation ->
    ('b, 'b2, 'c, 'd1) t -> ('a, 'b2, 'c, 'e) t

  val fork :
    ('a, 'b, 'c, 'd) t ->
    ('a, 'b, 'c, 'd) t ->
    ('a, 'b, 'c, 'd) t

  val fork_l :
    ('a, 'b, 'c, 'd) t list ->
    ('a, 'b, 'c, 'd) t

  val fork_comp :
    ('a, 'b, 'd1, 'e) transformation list ->
    ('b, 'b2, 'c, 'd1) t -> ('a, 'b2, 'c, 'e) t

  val check : _ t -> unit
  (** [check pipe] checks that the features of each component of
      the pipeline fit with their input.
      It is assumed we start with {!Features.full} *)

  val print : _ t printer
end

val run : pipe:('a, 'b, 'c, 'd) Pipe.t ->
          'a ->
          ('b * ('c -> 'd)) Lazy_list.t
(** [run ~pipe x] runs [x] through the pipe [pipe], in a lazy way,
    and yields values of type ['b] along with a conversion function back *)
