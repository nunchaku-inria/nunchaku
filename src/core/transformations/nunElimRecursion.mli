
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

type inv1 = <ty:[`Mono]; eqn:[`Linear]>
type inv2 = <ty:[`Mono]; eqn:[`Nested]>

module Make(T : NunTermInner.S) : sig
  type term = T.t
  type decode_state

  val elim_recursion :
    (term, term, inv1) NunProblem.t ->
    (term, term, inv2) NunProblem.t * decode_state

  val decode_term : state:decode_state -> term -> term

  val decode_model : state:decode_state -> term NunModel.t -> term NunModel.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, inv1) NunProblem.t,
      (term, term, inv2) NunProblem.t,
      term NunModel.t, term NunModel.t) NunTransform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_term:(term -> term) -> 'c -> 'd) ->
    print:bool ->
    ((term, term, inv1) NunProblem.t,
      (term, term, inv2) NunProblem.t,
      'c, 'd
    ) NunTransform.t
end

