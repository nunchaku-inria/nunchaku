
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

open Nunchaku_core

type id = ID.t

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

type ('a,'b) inv1 = <ty:[`Poly]; eqn:'a; ind_preds:'b>
type ('a,'b) inv2 = <ty:[`Mono]; eqn:'a; ind_preds:'b>

val name : string

exception InvalidProblem of string

module Make(T : TermInner.S) : sig
  type term = T.t

  type unmangle_state
  (** State used to un-mangle specialized symbols *)

  val monomorphize :
    ?depth_limit:int ->
    (term, term, ('a,'b) inv1) Problem.t ->
    (term, term, ('a,'b) inv2) Problem.t * unmangle_state
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

  val unmangle_term : state:unmangle_state -> term -> term
  (** Unmangle a single term: replace mangled constants by their definition *)

  val unmangle_model :
      state:unmangle_state ->
      (term,term) Model.t ->
      (term,term) Model.t
  (** Unmangles constants that have been collapsed with their type arguments *)

  val pipe :
    print:bool ->
    check:bool ->
    ((term, term, ('a,'b) inv1) Problem.t,
     (term, term, ('a,'b) inv2) Problem.t,
      (term,term) Problem.Res.t, (term,term) Problem.Res.t
    ) Transform.t
  (** Pipeline component *)

  val pipe_with :
    decode:(unmangle_state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((term, term, ('a,'b) inv1) Problem.t,
     (term, term, ('a,'b) inv2) Problem.t, 'c, 'd
    ) Transform.t
  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
end
