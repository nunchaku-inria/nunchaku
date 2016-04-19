
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core

module T = FO.T
module Ty = FO.Ty

type problem = FO_rel.problem
type res = (FO_rel.expr, FO_rel.expr) Problem.Res.t

val call :
  ?options:string ->
  ?timeout:float ->
  ?print:bool ->
  problem ->
  (res * Scheduling.shortcut) Scheduling.Fut.t
(** [solve pb] returns a {b task} that, when executed, will return
    a model or UNSAT (see {!Solver_intf.Res.t}). *)

val is_available : unit -> bool
(** test whether the solver is available (e.g. if the library is
      installed, or the binary in the path) *)

val pipe :
  ?print_model:bool ->
  print:bool ->
  unit ->
  ( problem,
    res Scheduling.Task.t,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling Kodkod on
    the input problem *)

