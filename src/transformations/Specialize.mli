
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Specialization}

  Specialization replaces some function, argument to another (higher-order) function,
  by its definition. It only works when the argument is known.

  Example:

  {[ let rec map f l = match l with
     | [] -> []
     | x::l2 -> f x :: map f l2

    map (fun x -> x+ g(x)) l
  ]}

  is converted into

  {[
  let rec map_357 l = match l with
    | [] -> []
    | x::l2 -> (x + g(x)) :: map_357 l2

    map_357 l
  ]}
*)

open Nunchaku_core

val name : string

exception Error of string

type inv = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

module Make(T : TermInner.S) : sig
  type term = T.t
  type ty = T.t

  type decode_state
  (** Used to decode *)

  val specialize_problem :
    (T.t, T.t, inv) Problem.t ->
    (T.t, T.t, inv) Problem.t * decode_state

  val decode_term : decode_state -> T.t -> T.t

  val pipe :
    print:bool ->
    check:bool ->
    ( (term, ty, inv) Problem.t,
      (term, ty, inv) Problem.t,
      (term, ty) Model.t, (term, ty) Model.t
    ) Transform.t

  val pipe_with :
    decode:(decode_state -> 'b -> 'c) ->
    print:bool ->
    check:bool ->
    ( (term, ty, inv) Problem.t,
      (term, ty, inv) Problem.t,
      'b, 'c
    ) Transform.t
end

