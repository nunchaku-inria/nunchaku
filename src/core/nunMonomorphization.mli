
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

type id = NunID.t

(* summary:
    - detect polymorphic functions
    - specialize them on some ground type (skolem?)
    - declare f_alpha : (typeof f) applied to alpha
    - add (f alpha) -> f_alpha in [rev]
    - rewrite (f alpha) into f_alpha everywhere

    - dependency analysis from the goal, to know which specialization
      are needed
    - variations on Axiom to help removing useless things
      ("spec" for consistent axioms that can be ignored,
      "def" for terminating ones that can be ignored (> spec), etc.)
*)

(** {2 Signature} *)
module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  exception InvalidProblem of string

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
    val is_empty : t -> bool
    val add : ArgTuple.t -> t -> t
    val to_list : t -> ArgTuple.t list
  end

  module SetOfInstances : sig
    type t

    val args : t -> id -> ArgTupleSet.t
    (** function -> set of args to instantiate it with *)

    val required : t -> id -> bool
    (** Is the symbol even needed? *)
  end

  val compute_instances :
    sigma:T1.ty NunProblem.Signature.t ->
    (T1.t, T1.ty) NunProblem.t ->
    SetOfInstances.t
  (** [compute_instances pb] finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples
      @param the signature of the symbols *)

  val monomorphize :
    instances:SetOfInstances.t ->
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

