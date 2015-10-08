
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

(** {2 Signature} *)
module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  (** {6 Set of Instances} *)

  (** Tuple of arguments to instantiate a symbol definition with *)
  module ArgTuple : sig
    type t
    val of_list : T2.ty list -> t
    val to_list : t -> T2.ty list
  end

  (** Set of {!ArgTuple.t} *)
  module ArgTupleSet : sig
    type t
    val empty : t
    val add : ArgTuple.t -> t -> t
    val to_list : t -> ArgTuple.t list
  end

  type set_of_instances =
    | NoInstances
    | Instances of ArgTupleSet.t

  val compute_instances :
    (T1.t, T1.ty) NunProblem.t ->
    set_of_instances NunID.Map.t
  (** [compute_instances pb] finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples *)

  val monomorphize :
    instances:set_of_instances NunID.Map.t ->
    (T1.t, T1.ty) NunProblem.t ->
    (T2.t, T2.ty) NunProblem.t
  (** Filter and specialize definitions of the problem using the given
      set of instances *)

  (** {6 Convert atomic types to symbols} *)
  module Mangling : sig
    type state
    (** Useful for decoding *)

    val create : unit -> state

    val mangle_term :
      state:state ->
      (T2.t,T2.ty) NunProblem.t ->
      (T2.t,T2.ty) NunProblem.t

    val mangle_problem :
      state:state ->
      (T2.t,T2.ty) NunProblem.t ->
      (T2.t,T2.ty) NunProblem.t

    val unmangle_term : state:state -> T2.t -> T2.t

    val unmangle_model :
        state:state ->
        T2.t NunProblem.Model.t -> T2.t NunProblem.Model.t
    (** Stay in the same term representation, but de-monomorphize *)
  end
end

module Make(T1 : NunTerm_ho.VIEW)(T2 : NunTerm_ho.S)
  : S with module T1 = T1 and module T2 = T2

