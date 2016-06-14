
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Analyze Types : Cardinalities, Abstract, Incomplete} *)

module TI = TermInner

exception Error of string

exception Polymorphic

exception EmptyData of ID.t

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

(** Approximation of a cardinal, including infinite cardinals *)
module Card : sig
  type t =
    | Exact of Z.t

    | QuasiFiniteGEQ of Z.t
        (** unknown, but ≥ 0. If all uninterpreted types are finite, then
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
end

module Make(T : TI.S) : sig
  type ty = T.t

  type 'a env = ('a, ty) Env.t
  (** We only consider monomorphic types *)

  type cache
  (** Cache for memoizing cardinality computations *)

  val create_cache : unit -> cache

  val cardinality_ty : ?cache:cache -> _ env -> ty -> Card.t
  (** [cardinality_ty ty] computes the cardinality of the type [ty], which
      must be monomorphic.
      @raise EmptyData if there is some ill-defined data in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val cardinality_ty_id : ?cache:cache -> _ env -> ID.t -> Card.t
  (** [cardinality id] computes the cardinality of the type
      named [id].
      @raise EmptyData if there is some ill-defined data in [env]
      @raise Error if [id] is not a valid type in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val check_non_zero :
    ?cache:cache -> 'a env -> ('a, ty) Statement.t -> unit
  (** [check_non_zero env stmt] checks that [stmt] is not a definition of
      an empty datatype *)

  val is_incomplete : _ env -> ty -> bool
  (** Is the type incomplete, that is, some values from the input type
      are not present in this encoding? *)

  val is_abstract : _ env -> ty -> bool
  (** Is the type a quotient over the input types (i.e. several distinct
      values of the input types are encoded as one value)? *)
end
