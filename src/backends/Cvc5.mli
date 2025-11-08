(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to cvc5} *)

open Nunchaku_core

type model_term = FO.T.t
type model_ty = FO.Ty.t
type problem = (model_term, model_ty) FO.Problem.t
type processed_problem

val preprocess : problem -> processed_problem
val pp_problem : Format.formatter -> processed_problem -> unit

val solve :
  ?options:string ->
  ?deadline:float ->
  ?print:bool ->
  ?print_model:bool ->
  env:(model_term, model_ty) FO.Env.t ->
  problem ->
  ((model_term, model_ty) Problem.Res.t * Scheduling.shortcut) Scheduling.Fut.t
(** [solve pb] returns a {b task} that, when executed, will return a model or
    UNSAT (see {!Solver_intf.Res.t}). *)

val is_available : unit -> bool
(** test whether the solver is available (e.g. if the library is installed, or
    the binary in the path) *)

exception Error of string
(** Error in the interface to cvc5 *)

val options_l : string list
(** list of different available options, starting with "" *)

val call :
  ?options:string ->
  ?prio:int ->
  ?slice:float ->
  print:bool ->
  dump:string option ->
  print_smt:bool ->
  print_model:bool ->
  env:(model_term, model_ty) FO.Env.t ->
  problem ->
  (model_term, model_ty) Problem.Res.t Scheduling.Task.t
(** Task for running cvc5 on a problem, with a set of options
    @return a tasks
    @param options: flags to pass the solver (default "").
    @param slice total amount of time allotted to cvc5
    @param prio priority of the task
    @param dump
      if [Some f], do not call the solver, but write the problem into file [f]
    @raise Cvc5_error if the solver failed with an error *)

val pipes :
  ?options:string list ->
  ?slice:float ->
  ?schedule_options:bool ->
  print:bool ->
  dump:string option ->
  print_smt:bool ->
  print_model:bool ->
  unit ->
  ( problem,
    (model_term, model_ty) Problem.Res.t Scheduling.Task.t list,
    'c,
    'c )
  Transform.transformation
(** Transformation corresponding to calling cvc5 on the input problem, with each
    set of option in [options].

    @param schedule_options
      if [true], then the time slice will be divided into smaller slices. Each
      slice is used by an instance of cvc5 with different parameters. Disable if
      you want the first instance(s) cvc5 to potentially use the full amount of
      time. *)
