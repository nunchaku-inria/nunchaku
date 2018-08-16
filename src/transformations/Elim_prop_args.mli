
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate function arguments of type "prop"}

    Emits some "if/then/else" instead, using a pseudo-prop type
    that has exactly two arguments. *)

open Nunchaku_core

type term = Term.t
type ty = term
type problem = (term, ty) Problem.t
type model = (term,ty) Model.t
type res = (term,ty) Problem.Res.t

val name : string

type state

val transform_problem : problem -> problem * state

val decode_model : state -> model -> model

val pipe_with :
  ?on_decoded:('b -> unit) list ->
  decode:(state -> 'a -> 'b) ->
  print:bool ->
  check:bool ->
  (problem, problem, 'a, 'b) Transform.t

val pipe :
  print:bool ->
  check:bool ->
  (problem, problem, res, res) Transform.t
