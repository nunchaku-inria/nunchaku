
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize}

  This duplicates some predicate definitions (either recursive equations,
  or (co)inductive specifications) depending on the call-site polarity.
*)

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val polarize :
    (term, term, 'a inv) Problem.t ->
    (term, term, 'a inv) Problem.t * decode_state

  val decode_model : state:decode_state -> term Model.t -> term Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      term Model.t, term Model.t) Transform.t

  (** Generic Pipe Component
      @param decode the decode function that takes an applied [(module S)]
        in addition to the state *)
  val pipe_with :
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    ((term, term, 'a inv) Problem.t,
      (term, term, 'a inv) Problem.t,
      'c, 'd
    ) Transform.t
end

