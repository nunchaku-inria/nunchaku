
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Backend for SMBC} *)

open Nunchaku_core

type term = TermInner.Default.t
type ty = term
type problem = (term,ty) Problem.t
type env = (term,ty) Env.t

val is_available : unit -> bool
(** test whether the solver is available *)

val call :
  ?print_model:bool ->
  ?prio:int ->
  print:bool ->
  dump:string option ->
  problem ->
  (term, ty) Problem.Res.t Scheduling.Task.t
(** Task for running smbc on a problem
    @return a tasks
    @param deadline absolute timestamp at which the process must have finished
    @param prio priority of the task
    @param dump if [Some f], do not call the solver, but write the problem into file [f]
*)

val pipe :
  ?print_model:bool ->
  print:bool ->
  dump:string option ->
  unit ->
  ( problem,
    (term, ty) Problem.Res.t Scheduling.Task.t,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling smbc on the problem *)

