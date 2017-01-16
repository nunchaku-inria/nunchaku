
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Frontend to Paradox} *)

open Nunchaku_core

type term = FO_tptp.term
type ty = FO_tptp.ty
type problem = FO_tptp.problem

val is_available : unit -> bool
(** test whether the solver is available *)

(** Task for running Paradox on a problem
    @return a tasks
    @param deadline absolute timestamp at which the process must have finished
    @param prio priority of the task
    @param dump if [Some f], do not call the solver, but write the problem into file [f]
*)
val call :
  ?print_model:bool ->
  ?prio:int ->
  print:bool ->
  dump:string option ->
  problem ->
  (term, ty) Problem.Res.t Scheduling.Task.t

val pipe :
  ?print_model:bool ->
  print:bool ->
  dump:string option ->
  unit ->
  ( problem,
    (term, ty) Problem.Res.t Scheduling.Task.t,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling paradox on the problem *)

