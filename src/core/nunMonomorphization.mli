
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

(* TODO: if depth limit reached, activate some "spuriousness" flag? *)

(** {2 Signature} *)
module type S = sig
  module T : NunTerm_ho.S

  exception InvalidProblem of string

  type mono_state
  (** State used for monomorphizing (to convert [f int (list nat)] to
      [f_int_list_nat], and back) *)

  val create : unit -> mono_state
  (** New state *)

  val monomorphize :
    ?depth_limit:int ->
    sigma:T.ty NunProblem.Signature.t ->
    state:mono_state ->
    (T.t, T.ty) NunProblem.t ->
    (T.t, T.ty) NunProblem.t
  (** Filter and specialize definitions of the problem.

      First it finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples.

      Then it specializes relevant definitions with the set of tuples
      computed earlier.

      @param sigma signature of the problem
      @param depth_limit recursion limit for specialization of functions
      @param state used to convert forward and backward *)

  val unmangle_model :
      state:mono_state ->
      T.t NunProblem.Model.t ->
      T.t NunProblem.Model.t
  (** Unmangles constants that have been collapsed with their type arguments *)

  (** {6 Convert atomic types to symbols}

    For instance, [list int] will become [list_int] or something similar.
    This operation is optional if the backend supports parametrized types. *)
  module TypeMangling : sig
    type state
    (** Useful for decoding *)

    val create : unit -> state

    val mangle_term :
      state:state ->
      (T.t,T.ty) NunProblem.t ->
      (T.t,T.ty) NunProblem.t

    val mangle_problem :
      state:state ->
      (T.t,T.ty) NunProblem.t ->
      (T.t,T.ty) NunProblem.t

    val unmangle_term : state:state -> T.t -> T.t

    val unmangle_model :
        state:state ->
        T.t NunProblem.Model.t -> T.t NunProblem.Model.t
    (** Stay in the same term representation, but de-monomorphize *)
  end
end

module Make(T : NunTerm_ho.S) : S with module T = T

(** Pipeline component *)
val pipe :
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t,
    'a NunProblem.Model.t, 'a NunProblem.Model.t) NunTransform.t

(** Pipeline component without model *)
val pipe_no_model :
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t, 'b, 'b) NunTransform.t

