
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

type t

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t

type fields
(** Set of boolean fields for some ID *)

val make : string -> t

val make_f : ('a, Format.formatter, unit, t) format4 -> 'a

val make_full :
  ?pol:Polarity.t ->
  ?distinct:bool ->
  needs_at:bool ->
  string ->
  t
(** Full constructor.
    @param pol polarity of ID (default: {!Polarity.NoPol})
    @param distinct if true, this ID will be consider as distinct from
      every other "distinct" ID for reduction purposes
    @param needs_at if true, the ID will be prefixed with a "\@" when
      printed with all its arguments. Usually needed by polymorphic values.
*)

val fresh_copy : t -> t
(** [fresh_copy v] makes a new identifier with the same name as [v] *)

val fresh_copy_name : t -> string -> t
(** [fresh_copy_name s id] builds a new copy of [id], but named [s] *)

val name : t -> string

val id : t -> int

val polarity : t -> Polarity.t
(** Obtain polarity of the id *)

val is_pos : t -> bool (** pol = Pos *)
val is_neg : t -> bool (** pol = Neg *)

val fields : t -> fields

val make_fields : ?pol:Polarity.t -> fields:fields -> string -> t
(** Build a new ID with the given fields and name *)

val is_polarized : t -> bool (** pol <> NoPol *)
val is_neutral : t -> bool (** Pol = NoPol *)

val needs_at : t -> bool
(** Should this ID be printed with a "\@"? *)

val is_distinct : t -> bool
(** Is this ID distinct from every other ID with the "distinct" property? *)

include Intf.PRINT with type t := t

val to_string : t -> string

val to_string_slug : t -> string
(** Pure alphanumerical identifier, see
    https://en.wikipedia.org/wiki/Semantic_URL#Slug *)

val print_full : Format.formatter -> t -> unit
(** Print with the unique integer ID *)

val to_string_full : t -> string

val print_name : Format.formatter -> t -> unit
(** Print only the name, nothing else *)

val print_undefined_id : bool ref
(** global option affecting printing: if true, undefined values will
    be displayed as "undefined_42" rather than "?__" *)

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
