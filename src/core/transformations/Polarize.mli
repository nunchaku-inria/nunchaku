
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize}

  This duplicates some predicate definitions (either recursive equations,
  or (co)inductive specifications) depending on the call-site polarity.
*)

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

val name : string

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  (** Polarize inductive predicates and possibly some other predicates
      in the problem.
      @param polarize_rec if true, some propositions defined with `rec`
        might be polarized *)
  val polarize :
    polarize_rec:bool ->
    (term, term, 'a inv) Problem.t ->
    (term, term, 'a inv) Problem.t * decode_state

  val decode_model : state:decode_state -> (term,term) Model.t -> (term,term) Model.t

  (** Pipeline component *)
  val pipe :
    polarize_rec:bool ->
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      (term, term) Model.t, (term, term) Model.t) Transform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    polarize_rec:bool ->
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      'c, 'd
    ) Transform.t
end

