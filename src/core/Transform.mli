
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a printer = 'a CCFormat.printer

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

  val print : _ t printer
end

val run : pipe:('a, 'b, 'c, 'd) Pipe.t ->
          'a ->
          ('b * ('c -> 'd)) Lazy_list.t
(** [run ~pipe x] runs [x] through the pipe [pipe], in a lazy way,
    and yields values of type ['b] along with a conversion function back *)
