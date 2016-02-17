
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4.
    It encodes recursive functions as axioms, with a quantification over
    an uninterpreted abstraction type. *)

type inv1 = <ty:[`Mono]; eqn:[`Single]; ind_preds:[`Absent]>
type inv2 = <ty:[`Mono]; eqn:[`Absent]; ind_preds:[`Absent]>

val name : string

exception Attr_abs_type of ID.t
(** The annotated ID is an abstraction type (handle) for the given function symbol *)

exception Attr_abs_projection of ID.t * int
(** [Attr_abs_projection (handle, n)]
    The annotated ID is the n-th projection from the given handle ID *)

module Make(T : TermInner.S) : sig
  type term = T.t
  type decode_state

  val elim_recursion :
    (term, term, inv1) Problem.t ->
    (term, term, inv2) Problem.t * decode_state

  val decode_model :
    state:decode_state ->
    (term, term) Model.t ->
    (term, term) Model.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, inv1) Problem.t,
      (term, term, inv2) Problem.t,
      (term, term) Model.t,
      (term, term) Model.t) Transform.t

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

