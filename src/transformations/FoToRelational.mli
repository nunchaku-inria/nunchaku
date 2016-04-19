
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

type state

val pipe_with :
  decode:(state -> 'a -> 'b) ->
  print:bool ->
  ( (FO.T.t, FO.Ty.t) FO.Problem.t,
    (FO.T.t, FO.Ty.t) FO.Problem.t,
    'a, 'b
  ) Transform.t

val pipe :
  print:bool ->
  ( (FO.T.t, FO.Ty.t) FO.Problem.t,
    (FO.T.t, FO.Ty.t) FO.Problem.t,
    (FO.T.t, FO.Ty.t) Problem.Res.t,
    (FO.T.t, FO.Ty.t) Problem.Res.t
  ) Transform.t

