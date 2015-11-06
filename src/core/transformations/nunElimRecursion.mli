
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

type invariant = <poly:[`Mono]; meta:[`NoMeta]>

module Make(T : NunTerm_ho.S) : sig
  type term = invariant T.t
  type decode_state

  val elim_recursion :
    (term, term, [`Linear]) NunProblem.t ->
    (term, term, [`Linear]) NunProblem.t * decode_state

  val decode_term : state:decode_state -> term -> term

  val decode_model : state:decode_state -> term NunModel.t -> term NunModel.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, [`Linear]) NunProblem.t,
      (term, term, [`Linear]) NunProblem.t,
      term NunModel.t, term NunModel.t) NunTransform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_term:(term -> term) -> 'c -> 'd) ->
    print:bool ->
    ((term, term, [`Linear]) NunProblem.t,
      (term, term, [`Linear]) NunProblem.t,
      'c, 'd
    ) NunTransform.t
end

