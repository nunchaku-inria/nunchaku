
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

type invariant1 = <meta:NunMark.without_meta; poly:NunMark.polymorph>
type invariant2 = <meta:NunMark.without_meta; poly:NunMark.monomorph>

module type PARAM = sig
  type term1
  type term2

  val build1: (term1, invariant1) NunTerm_ho.build
  val build2: (term2, invariant2) NunTerm_ho.build
end

module Make(P : PARAM) : sig
  type term1 = P.term1
  type term2 = P.term2

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
end

(** {2 Convert atomic types to symbols}

  For instance, [list int] will become [list_int] or something similar.
  This operation is optional if the backend supports parametrized types. *)
module TypeMangling : sig
  type 't state
  (** Useful for decoding *)

  val create : build:('t, _) NunTerm_ho.build -> unit -> 't state

  val mangle_term :
    state:'t state ->
    't ->
    't

  val mangle_problem :
    state:' state ->
    ('t,'t,'inv) NunProblem.t ->
    ('t,'t,'inv) NunProblem.t

  val unmangle_term : state:'t state -> 't -> 't

  val unmangle_model :
      state:'t state ->
      't NunModel.t -> 't NunModel.t
  (** Stay in the same term representation, but de-monomorphize *)
end

(** Pipeline component *)
val pipe :
  print:bool ->
  build1:('t1, invariant1) NunTerm_ho.build ->
  build2:('t2, invariant2) NunTerm_ho.build ->
  (('t1, 't1, 'inv) NunProblem.t,
    ('t2, 't2, 'inv) NunProblem.t,
    't1 NunModel.t, 't1 NunModel.t
  ) NunTransform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  decode:(decode_term:('t2 -> 't1) -> 'c -> 'd) ->
  print:bool ->
  build1:('t1, invariant1) NunTerm_ho.build ->
  build2:('t2, invariant2) NunTerm_ho.build ->
  (('t1, 't1, 'inv) NunProblem.t, ('t2,'t2,'inv) NunProblem.t, 'c, 'd) NunTransform.t

