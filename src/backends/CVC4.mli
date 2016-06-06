
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

open Nunchaku_core

module T = FO.T
module Ty = FO.Ty

type model_term = T.t
type model_ty = Ty.t

type problem = (T.t, Ty.t) FO.Problem.t
type processed_problem

val preprocess : problem -> processed_problem

val print_problem : Format.formatter -> processed_problem -> unit

val solve :
  ?options:string ->
  ?deadline:float ->
  ?print:bool ->
  ?print_model:bool ->
  problem ->
  ((T.t, Ty.t) Problem.Res.t * Scheduling.shortcut) Scheduling.Fut.t
  (** [solve pb] returns a {b task} that, when executed, will return
      a model or UNSAT (see {!Solver_intf.Res.t}). *)

val is_available : unit -> bool
(** test whether the solver is available (e.g. if the library is
      installed, or the binary in the path) *)

(** Error in the interface to CVC4 *)
exception Error of string

(** Error from CVC4 itself *)
exception CVC4_error of string

(** list of different available options, starting with "" *)
val options_l : string list

(** Task for running CVC4 on a problem, with a set of options
  @return a tasks
  @param options: flags to pass the solver (default "").
  @param slice total amount of time allotted to CVC4
  @param prio priority of the task
  @raise CVC4_error if the solver failed with an error
*)
val call :
  ?options:string ->
  ?prio:int ->
  ?slice:float ->
  print:bool ->
  print_smt:bool ->
  print_model:bool ->
  problem ->
  (model_term, model_ty) Problem.Res.t Scheduling.Task.t

val pipes :
  ?options:string list ->
  ?slice:float ->
  print:bool ->
  print_smt:bool ->
  print_model:bool ->
  unit ->
  ( problem,
    (model_term, model_ty) Problem.Res.t Scheduling.Task.t list,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling CVC4 on
    the input problem, with each set of option in [options] *)

