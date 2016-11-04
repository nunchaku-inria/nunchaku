
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Cardinalities} *)

module Z : sig
  type t = Big_int.big_int
  val zero : t
  val of_int : int -> t
  val to_int : t -> int option
  val one : t
  val sign : t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
  val pp_print : t CCFormat.printer
  val compare : t -> t -> int
  val hash : t -> int
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
end

type t =
  | Exact of Z.t
  | QuasiFiniteGEQ of Z.t
      (** unknown, but ≥ Z.t value. If all uninterpreted types are finite, then
          this is finite too *)
  | Infinite
  | Unknown
      (** Any value, we do not know *)

val (+) : t -> t -> t
val ( * ) : t -> t -> t
val zero : t
val one : t
val of_int : int -> t
val of_z : Z.t -> t

val is_zero : t -> bool
val is_finite : t -> bool

val sum : t list -> t
val product : t list -> t

val infinite : t
val unknown : t
val quasi_finite_geq : Z.t -> t
val quasi_finite_zero : t (** anything ≥ 0 *)
val quasi_finite_nonzero : t (** ≥ 1 *)

include Intf.EQ with type t := t
include Intf.HASH with type t := t
val print : t CCFormat.printer
