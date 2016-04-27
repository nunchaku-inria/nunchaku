
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Simple Types} *)

open Nunchaku_core

module TI = TermInner

type inv = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

module Make(T : TI.S) : sig
  type state

  val transform_pb :
    (T.t, T.t, inv) Problem.t ->
    (T.t, T.t, inv) Problem.t * state

  val decode_model :
    state:state -> (T.t,T.t) Model.t -> (T.t,T.t) Model.t

  val pipe :
    print:bool ->
    check:bool ->
    ((T.t,T.t,inv) Problem.t,
     (T.t,T.t,inv) Problem.t,
      (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
    ) Transform.t

  val pipe_with :
    decode:(state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((T.t,T.t,inv) Problem.t,
     (T.t,T.t,inv) Problem.t, 'c, 'd
    ) Transform.t
end
