
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate function arguments of type "prop"}

    Emits some "if/then/else" instead, using a pseudo-prop type
    that has exactly two arguments. *)

open Nunchaku_core

module T = TermInner.Default

type inv = <ind_preds:[`Absent]; ty:[`Mono]; eqn:[`Absent]>

type term = T.t
type ty = T.t
type problem = (term, ty, inv) Problem.t
type model = (term,ty) Model.t
type res = (term,ty) Problem.Res.t

val name : string

type state

val transform_problem : problem -> problem * state

val decode_model : state -> model -> model

val pipe_with :
  decode:(state -> 'a -> 'b) ->
  print:bool ->
  check:bool ->
  (problem, problem, 'a, 'b) Transform.t

val pipe :
  print:bool ->
  check:bool ->
  (problem, problem, res, res) Transform.t
