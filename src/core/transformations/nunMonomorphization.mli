
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

type inv1 = <meta:[`NoMeta]; poly:[`Poly]>
type inv2 = <meta:[`NoMeta]; poly:[`Mono]>

module Make(T : NunTerm_ho.S) : sig
  type term1 = inv1 T.t
  type term2 = inv2 T.t

  exception InvalidProblem of string

  type unmangle_state
  (** State used to un-mangle specialized symbols *)

  val monomorphize :
    ?depth_limit:int ->
    (term1, term1, 'inv) NunProblem.t ->
    (term2, term2, 'inv) NunProblem.t * unmangle_state
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

  val unmangle_term : state:unmangle_state -> term2 -> term1
  (** Unmangle a single term: replace mangled constants by their definition *)

  val unmangle_model :
      state:unmangle_state ->
      term2 NunModel.t ->
      term1 NunModel.t
  (** Unmangles constants that have been collapsed with their type arguments *)

  val pipe :
    print:bool ->
    ((term1, term1, 'inv) NunProblem.t,
      (term2, term2, 'inv) NunProblem.t,
      term2 NunModel.t, term1 NunModel.t
    ) NunTransform.t
  (** Pipeline component *)

  val pipe_with :
    decode:(decode_term:(term2 -> term1) -> 'c -> 'd) ->
    print:bool ->
    ((term1, term1, 'inv) NunProblem.t,
      (term2, term2, 'inv) NunProblem.t, 'c, 'd
    ) NunTransform.t
  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
end
