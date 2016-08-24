
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Analyze Types : Cardinalities, Abstract, Incomplete} *)

exception Error of string

exception Polymorphic

exception EmptyData of ID.t

module Make(T : TermInner.S) : sig
  type ty = T.t

  type 'a env = ('a, ty) Env.t
  (** We only consider monomorphic types *)

  type cache
  (** Cache for memoizing cardinality computations *)

  val create_cache :
    ?default_card:int ->
    ?map_hint:(Cardinality.t -> Cardinality.t option) ->
    unit ->
    cache
  (** @param default_card if provided, the uninterpreted types we
        know nothing about will be considered as having this card
      @param map_hint if provided, will be applied to filter_map any
        type hint associated with uninterpreted types *)

  val cardinality_ty : ?cache:cache -> _ env -> ty -> Cardinality.t
  (** [cardinality_ty ty] computes the cardinality of the type [ty], which
      must be monomorphic.
      @raise EmptyData if there is some ill-defined data in [env]
      @raise Polymorphic if the type is polymorphic,
        or depends on polymorphic types *)

  val cardinality_ty_id : ?cache:cache -> _ env -> ID.t -> Cardinality.t
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
