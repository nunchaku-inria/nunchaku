
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unrolling of (co)inductive Predicates} *)

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

val name : string

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val unroll :
    (term, term, 'a inv) Problem.t ->
    (term, term, 'a inv) Problem.t * decode_state

  val decode_model :
    state:decode_state -> (term,term) Model.t -> (term,term) Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      (term, term) Model.t, (term, term) Model.t) Transform.t

  (** Generic Pipe Component *)
  val pipe_with :
    ?on_decoded:(('d -> unit) list) ->
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      'c, 'd
    ) Transform.t
end
