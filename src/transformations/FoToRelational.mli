
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

type problem1 = (FO.T.t, FO.Ty.t) FO.Problem.t
type model1 = (FO.T.t, FO.Ty.t) Model.t

type problem2 = FO_rel.problem
type model2 = (FO_rel.expr, FO_rel.sub_universe) Model.t

val name: string

(** {2 Encoding} *)

type state

val encode_pb : problem1 -> problem2 * state

(** {2 Decoding} *)

val decode : state -> model2 -> model1

(** {2 Pipes} *)

(** We assume there is a type with flag "pseudo-prop" somewhere *)

val pipe_with :
  ?on_decoded:('b -> unit) list ->
  decode:(state -> 'a -> 'b) ->
  print:bool ->
  (problem1, problem2, 'a, 'b) Transform.t

val pipe :
  print:bool ->
  ( problem1,
    problem2,
    (FO_rel.expr, FO_rel.sub_universe) Problem.Res.t,
    (FO.T.t, FO.Ty.t) Problem.Res.t
  ) Transform.t

