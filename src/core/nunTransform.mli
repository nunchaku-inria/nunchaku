
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pipeline of Transformations} *)

type 'a lazy_list = unit -> [`Nil | `Cons of 'a * 'a lazy_list]
(** A lazy list of values of type ['a] *)

(** {2 Single Transformation} *)

(** Transformation of ['a] to ['b]. The transformation make choices by
    lazily returning several values. It is also allowed to store data
    in a internal "state" type, to be able to transform back later. *)
type ('a, 'b) t = Ex : ('a, 'b, 'st) inner -> ('a, 'b) t

(** Transformation with explicit hidden state *)
and ('a, 'b, 'st) inner = {
  name : string; (** informal name for the transformation *)
  encode : 'a -> ('b * 'st) lazy_list;
  decode : 'st -> 'b -> 'a;
  print_state : (Format.formatter -> 'st -> unit) option;  (** Debugging *)
}

type ('a, 'b) transformation = ('a, 'b) t
(** Alias to {!t} *)


(** {2 Pipeline of Transformations}

    Allows chaining the transformations in a type-safe way *)

module Pipe : sig
  (** Composite transformation from ['a] to ['b], yielding results ['res] *)
  type ('a, 'b, 'res) t =
    | Id : ('a, 'a, unit) t  (** no transformation *)
    | Call : ('a -> ('a option * 'res) lazy_list) -> ('a, 'a, 'res) t
    | Comp : ('a, 'b) transformation * ('b, 'c, 'res) t -> ('a, 'c, 'res) t

  (* TODO: replace/complement Id by the function from {!run}, b -> (b option * res) list *)

  val id : ('a, 'a, unit) t

  val compose : ('a, 'b) transformation -> ('b, 'c, 'res) t -> ('a, 'c, 'res) t

  val call :
    ('a, 'b, _) t ->
    f:('b -> ('b option * 'res) lazy_list) ->
    ('a, 'b, 'res) t
  (** [call p ~f] is the same pipe as [p], but calls [f] on each
      value [y] obtained through the pipe to obtain a result and a possible
      new value of type ['b]. *)
end

val run : pipe:('a, 'b, 'res) Pipe.t -> 'a -> ('a option * 'res) lazy_list
(** [run ~pipe x ~f] runs [x] through the pipe [pipe], in a lazy way,
    and converts back each resulting [y: 'b] (if any) into a ['a] along
    with the result. *)


