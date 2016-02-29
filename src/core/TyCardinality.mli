
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner

exception Error of string

exception Polymorphic

exception EmptyData of ID.t

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

  type ('a, 'inv) env = ('a, ty, 'inv) Env.t constraint 'inv = <ty:[`Mono]; ..>
  (** We only consider monomorphic types *)

  type cache
  (** Cache for memoizing cardinality computations *)

  val create_cache : unit -> cache

  val cardinality_ty : ?cache:cache -> (_, _) env -> ty -> Card.t
  (** [cardinality_ty ty] computes the cardinality of the type [ty], which
      must be monomorphic.
      @raise EmptyData if there is some ill-defined data in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val cardinality_ty_id : ?cache:cache -> (_, _) env -> ID.t -> Card.t
  (** [cardinality id] computes the cardinality of the type
      named [id].
      @raise EmptyData if there is some ill-defined data in [env]
      @raise Error if [id] is not a valid type in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val check_non_zero :
    ?cache:cache -> ('a, 'inv) env -> ('a, ty, 'inv) Statement.t -> unit
  (** [check_non_zero env stmt] checks that [stmt] is not a definition of
      an empty datatype *)
end
