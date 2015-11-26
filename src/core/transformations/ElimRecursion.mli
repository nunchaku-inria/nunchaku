
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4 *)

type inv1 = <ty:[`Mono]; eqn:[`Linear]>
type inv2 = <ty:[`Mono]; eqn:[`Nested]>

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val elim_recursion :
    (term, term, inv1) Problem.t ->
    (term, term, inv2) Problem.t * decode_state

  val decode_model : state:decode_state -> term Model.t -> term Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, inv1) Problem.t,
      (term, term, inv2) Problem.t,
      term Model.t, term Model.t) Transform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    ((term, term, inv1) Problem.t,
      (term, term, inv2) Problem.t,
      'c, 'd
    ) Transform.t
end

