
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lambda Lifting}

    Remaining λ expressions are extracted as toplevel {b named} functions *)

type inv = <ty:[`Mono]; ind_preds:[`Absent]; eqn:[`Single]>

val name : string

module Make(T : TermInner.S) : sig
  type state

  val tr_problem :
    state:state ->
    (T.t, T.t, inv) Problem.t ->
    (T.t, T.t, inv) Problem.t

  val decode_model :
    state:state -> (T.t,T.t) Model.t -> (T.t,T.t) Model.t

  val pipe :
    print:bool ->
    check:bool ->
    ((T.t,T.t,inv) Problem.t,
      (T.t,T.t,inv) Problem.t,
      (T.t,T.t) Model.t, (T.t,T.t) Model.t
    ) Transform.t

  (** Similar to {!pipe} but with a generic decode function.
      @param print if true, prints problem after lifting
      @param check if true, check the invariants on the result *)
  val pipe_with :
    decode:(state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((T.t,T.t, inv) Problem.t,
      (T.t,T.t,inv) Problem.t, 'c, 'd
    ) Transform.t
end
