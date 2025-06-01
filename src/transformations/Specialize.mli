
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Specialization}

    Specialization replaces some function, argument to another (higher-order) function,
    by its definition. It only works when the argument is known.

    Example:

    {[ let rec map f l = match l with
        | [] -> []
        | x::l2 -> f x :: map f l2 ;;

      map (fun x -> x+ g(x)) l
    ]}

    is converted into

    {[
      let rec map_357 l = match l with
        | [] -> []
        | x::l2 -> (x + g(x)) :: map_357 l2 ;;

      map_357 l
    ]}
*)

open Nunchaku_core

val name : string

exception Error of string

type term = Term.t
type ty = term

type decode_state
(** Used to decode *)

val specialize_problem :
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state

val decode_term : decode_state -> term -> term

val pipe :
  print:bool ->
  check:bool ->
  ( (term, ty) Problem.t,
    (term, ty) Problem.t,
    (term, ty) Problem.Res.t, (term, ty) Problem.Res.t
  ) Transform.t

val pipe_with :
  ?on_decoded:('c -> unit) list ->
  decode:(decode_state -> 'b -> 'c) ->
  print:bool ->
  check:bool ->
  unit ->
  ( (term, ty) Problem.t,
    (term, ty) Problem.t,
    'b, 'c
  ) Transform.t

