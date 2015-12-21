
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

type t

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t

val make : string -> t

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

val print_full : Format.formatter -> t -> unit
(** Print with the unique integer ID *)

val print_name : Format.formatter -> t -> unit
(** Print only the name, nothing else *)

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t
module PerTbl : CCPersistentHashtbl.S with type key = t
