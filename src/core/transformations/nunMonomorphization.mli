
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

module Make(T : NunTerm_ho.S) : sig
  exception InvalidProblem of string

  type unmangle_state
  (** State used to un-mangle specialized symbols *)

  val monomorphize :
    ?depth_limit:int ->
    (T.t, T.ty) NunProblem.t ->
    (T.t, T.ty) NunProblem.t * unmangle_state
  (** Filter and specialize definitions of the problem.

      First it finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples.

      Then it specializes relevant definitions with the set of tuples
      computed earlier.

      @param depth_limit recursion limit for specialization of functions
      @return a new list of (monomorphized) statements, and the final
        state obtained after monomorphization
  *)

  val unmangle_term : state:unmangle_state -> T.t -> T.t
  (** Unmangle a single term: replace mangled constants by their definition *)

  val unmangle_model :
      state:unmangle_state ->
      T.t NunModel.t ->
      T.t NunModel.t
  (** Unmangles constants that have been collapsed with their type arguments *)
end

(** {2 Convert atomic types to symbols}

  For instance, [list int] will become [list_int] or something similar.
  This operation is optional if the backend supports parametrized types. *)
module TypeMangling(T : NunTerm_ho.S) : sig
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
      T.t NunModel.t -> T.t NunModel.t
  (** Stay in the same term representation, but de-monomorphize *)
end

(** Pipeline component *)
val pipe :
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t,
    'a NunModel.t, 'a NunModel.t) NunTransform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  decode:(decode_term:('a -> 'a) -> 'c -> 'd) ->
  print:bool ->
  (module NunTerm_ho.S with type t = 'a) ->
  (('a, 'a) NunProblem.t, ('a,'a) NunProblem.t, 'c, 'd) NunTransform.t

