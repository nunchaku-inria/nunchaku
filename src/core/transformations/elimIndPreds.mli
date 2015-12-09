
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates}

  Encode them as recursive functions, see
  https://github.com/nunchaku-inria/nunchaku/issues/4
*)

type 'a inv1 = <eqn:'a; ty:[`Mono]; ind_preds:[`Present]>
type 'a inv2 = <eqn:'a; ty:[`Mono]; ind_preds:[`Absent]>

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val elim_ind_preds :
    (term, term, 'a inv1) Problem.t ->
    (term, term, 'a inv2) Problem.t * decode_state

  val decode_model : state:decode_state -> term Model.t -> term Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, 'a inv1) Problem.t,
      (term, term, 'a inv2) Problem.t,
      term Model.t, term Model.t) Transform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    ((term, term, 'a inv1) Problem.t,
      (term, term, 'a inv2) Problem.t,
      'c, 'd
    ) Transform.t
end

