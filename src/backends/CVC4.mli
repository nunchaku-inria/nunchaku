
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

open Nunchaku_core

module Make(F : FO.S) : sig
  include Solver_intf.S
  with module FO_T = F
  and module FOBack = FO.Default

  type processed_problem

  val preprocess : problem -> processed_problem

  val print_problem : Format.formatter -> processed_problem -> unit

  val solve :
    ?options:string ->
    ?deadline:float ->
    ?print:bool ->
    problem ->
    ((FOBack.T.t, FOBack.Ty.t) Problem.Res.t * Scheduling.shortcut) Scheduling.Fut.t
  (** [solve pb] returns a {b task} that, when executed, will return
      a model or UNSAT (see {!Solver_intf.Res.t}). *)
end

type model_term = FO.Default.T.t
type model_ty = FO.Default.Ty.t

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
  @param deadline absolute timestamp at which the process must have finished
  @param prio priority of the task
  @raise CVC4_error if the solver failed with an error
*)
val call :
  (module FO.S with type T.t = 't and type Ty.t = 'ty) ->
  ?options:string ->
  ?deadline:float ->
  ?prio:int ->
  print:bool ->
  print_smt:bool ->
  ('t, 'ty) FO.Problem.t ->
  (model_term, model_ty) Problem.Res.t Scheduling.Task.t

val pipes :
  (module FO.S with type T.t = 't and type Ty.t = 'ty) ->
  ?options:string list ->
  ?deadline:float ->
  print:bool ->
  print_smt:bool ->
  unit ->
  ( ('t, 'ty) FO.Problem.t,
    (model_term, model_ty) Problem.Res.t Scheduling.Task.t list,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling CVC4 on
    the input problem, with each set of option in [options] *)

