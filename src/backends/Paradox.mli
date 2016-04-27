
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Frontend to Paradox} *)

open Nunchaku_core

module T = FO_tptp

val is_available : unit -> bool
(** test whether the solver is available *)

(** Task for running Paradox on a problem
  @return a tasks
  @param deadline absolute timestamp at which the process must have finished
  @param prio priority of the task
*)
val call :
  ?deadline:float ->
  ?prio:int ->
  print:bool ->
  T.problem ->
  (T.term, T.ty) Problem.Res.t Scheduling.Task.t

val pipe :
  ?deadline:float ->
  print:bool ->
  unit ->
  ( T.problem,
    (T.term, T.ty) Problem.Res.t Scheduling.Task.t,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling paradox on the problem *)

