
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to Kodkod} *)

open Nunchaku_core

module T = FO.T
module Ty = FO.Ty

type problem = (T.t, Ty.t) FO.Problem.t

val call :
  ?options:string ->
  ?timeout:float ->
  ?print:bool ->
  problem ->
  ((T.t, Ty.t) Problem.Res.t * Scheduling.shortcut) Scheduling.Fut.t
(** [solve pb] returns a {b task} that, when executed, will return
    a model or UNSAT (see {!Solver_intf.Res.t}). *)

val is_available : unit -> bool
(** test whether the solver is available (e.g. if the library is
      installed, or the binary in the path) *)

val pipe :
  ?deadline:float ->
  print:bool ->
  unit ->
  ( problem,
    (T.t, Ty.t) Problem.Res.t Scheduling.Task.t,
    'c, 'c) Transform.transformation
(** Transformation corresponding to calling Kodkod on
    the input problem *)

