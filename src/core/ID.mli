
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

type t

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t

val make : string -> t

val make_f : ('a, Format.formatter, unit, t) format4 -> 'a

val make_full : ?pol:Polarity.t -> needs_at:bool -> string -> t

val fresh_copy : t -> t
(** [fresh_copy v] makes a new identifier with the same name as [v] *)

val name : t -> string

val id : t -> int

val polarity : t -> Polarity.t
(** Obtain polarity of the id *)

val is_pos : t -> bool (** pol = Pos *)
val is_neg : t -> bool (** pol = Neg *)
val is_polarized : t -> bool (** pol <> NoPol *)
val is_neutral : t -> bool (** Pol = NoPol *)

val needs_at : t -> bool
(** Should this ID be printed with a "@"? *)

include Intf.PRINT with type t := t

val to_string : t -> string

val to_string_slug : t -> string
(** Pure alphanumerical identifier, see
    https://en.wikipedia.org/wiki/Semantic_URL#Slug *)

val print_full : Format.formatter -> t -> unit
(** Print with the unique integer ID *)

val print_name : Format.formatter -> t -> unit
(** Print only the name, nothing else *)

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t
module PerTbl : CCPersistentHashtbl.S with type key = t

(** Map to unique names *)
module Erase : sig
  type state

  val create_state: unit -> state

  val add_name : state -> string -> t -> unit
  (** Add the mapping [name <=> id] to the state. It will shadow
      the previous binding of [name], if any.
      @raise Invalid_argument if [id] is already bound *)

  val to_name : ?encode:(t -> string -> string) -> state -> t -> string
  (** [to_name state id] maps [id] to a unique name, and remembers the
      inverse mapping so that [of_name state (to_name state id) = id].
      @param encode a function to transform the name before remembering it *)

  val of_name : state -> string -> t
  (** @raise Not_found if the name corresponds to no ID *)
end
