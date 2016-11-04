(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core

type problem = FO_rel.problem
type res = (FO_rel.expr, FO_rel.sub_universe) Problem.Res.t

val call :
  ?print_model:bool ->
  ?prio:int ->
  print:bool ->
  problem ->
  res Scheduling.Task.t

val is_available : unit -> bool
(** test whether the solver is available (e.g. if the library is
      installed, or the binary in the path) *)

val pipe :
  ?print_model:bool ->
  print:bool ->
  unit ->
  ( problem,
    res Scheduling.Task.t,
    'c, 'c) Transform.t
(** Transformation corresponding to calling Kodkod on
    the input problem *)
