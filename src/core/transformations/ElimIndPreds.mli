
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates}

  Encode them as recursive functions, see
  https://github.com/nunchaku-inria/nunchaku/issues/4
*)

type inv1 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Present]>
type inv2 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

val name : string

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val elim_ind_preds :
    (term, term, inv1) Problem.t ->
    (term, term, inv2) Problem.t * decode_state

  val decode_model : state:decode_state -> (term,term) Model.t -> (term,term) Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    check:bool ->
    ((term, term, inv1) Problem.t,
      (term, term, inv2) Problem.t,
      (term,term) Model.t, (term,term) Model.t) Transform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((term, term, inv1) Problem.t,
      (term, term, inv2) Problem.t,
      'c, 'd
    ) Transform.t
end

