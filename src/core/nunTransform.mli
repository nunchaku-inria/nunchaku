
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a lazy_list = unit -> [`Nil | `Cons of 'a * 'a lazy_list]
(** A lazy list of values of type ['a] *)

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b], with reverse transformation from ['c]
    to ['d]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to perform the reverse
    transformation. *)
type ('a, 'b, 'c, 'd) t = Ex : ('a, 'b, 'c, 'd, 'st) inner -> ('a, 'b, 'c, 'd) t

(** Transformation with explicit hidden state *)
and ('a, 'b, 'c, 'd, 'st) inner = {
  name : string; (** informal name for the transformation *)
  encode : 'a -> ('b * 'st) lazy_list;
  decode : 'st -> 'c -> 'd;
  mutable on_input : ('a -> unit) list;
  mutable on_encoded : ('b -> unit) list;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b, 'c, 'd) transformation = ('a, 'b, 'c, 'd) t
(** Alias to {!t} *)

val make : ?print:(Format.formatter -> 'st -> unit) ->
           ?name:string ->
           ?on_input:('a -> unit) list ->
           ?on_encoded:('b -> unit) list ->
           encode:('a -> ('b * 'st) lazy_list) ->
           decode:('st -> 'c -> 'd) ->
           unit ->
           ('a, 'b, 'c, 'd) t
(** Constructor *)

val make1 : ?print:(Format.formatter -> 'st -> unit) ->
            ?name:string ->
            ?on_input:('a -> unit) list ->
            ?on_encoded:('b -> unit) list ->
            encode:('a -> 'b * 'st) ->
            decode:('st -> 'c -> 'd) ->
            unit ->
            ('a, 'b, 'c, 'd) t
(** Constructor when [encode] returns exactly one solution *)

val on_encoded : (_, 'b, _, _) t -> f:('b -> unit) -> unit
(** [on_encoded tr ~f] registers [f] to be called on every value
    obtained by encoding through [tr] *)

val on_input : ('a, _, _, _) t -> f:('a -> unit) -> unit

(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe : sig
  (** Composite transformation from ['a] to ['b], with a reverse transformation
      from ['c] to ['d] *)
  type ('a, 'b, 'c, 'd) t =
    | Id : ('a, 'a, 'c, 'c) t  (** no transformation *)
    | Comp : ('a, 'b, 'd, 'e) transformation * ('b, 'b2, 'c, 'd) t -> ('a, 'b2, 'c, 'e) t

  val id : ('a, 'a, 'c, 'c) t

  val compose :
    ('a, 'b, 'd1, 'e) transformation ->
    ('b, 'b2, 'c, 'd1) t -> ('a, 'b2, 'c, 'e) t

  val (@@@) :
    ('a, 'b, 'd1, 'e) transformation ->
    ('b, 'b2, 'c, 'd1) t -> ('a, 'b2, 'c, 'e) t
end

val run : pipe:('a, 'b, 'c, 'd) Pipe.t ->
          'a ->
          ('b * ('c -> 'd)) lazy_list
(** [run ~pipe x] runs [x] through the pipe [pipe], in a lazy way,
    and yields values of type ['b] along with a conversion function back *)

(** {2 Pipe with a function at the end}

  Same as composing a {!Pipe.t} with a function that consumes it and
  returns values to be converted back *)
module ClosedPipe : sig
  type ('a, 'c, 'd, 'res) t =
    | ClosedEx : ('a, 'b, 'c, 'd, 'res) inner -> ('a, 'c, 'd, 'res) t
  (** A machine that consumes ['a] using a pipeline, and calls some function
      to obtain a result ['res] and something that can be converted back
      to ['d] using the pipeline again *)

  and ('a, 'b, 'c, 'd, 'res) inner = {
    pipe: ('a, 'b, 'c, 'd) Pipe.t;
    call: ('b -> 'res lazy_list);
  }

  val make :
    pipe: ('a, 'b, 'c, 'd) Pipe.t ->
    f:('b -> 'res lazy_list) ->
    ('a, 'c, 'd, 'res) t

  val make1 :
    pipe: ('a, 'b, 'c, 'd) Pipe.t ->
    f:('b -> 'res) ->
    ('a, 'c, 'd, 'res) t
  (** Same as {!make}, but the function always returns exactly one element *)
end

val run_closed :
  cpipe:('a, 'c, 'd, 'res) ClosedPipe.t ->
  'a ->
  ('res * ('c -> 'd)) lazy_list
(** Run the value through [pipe] *)

