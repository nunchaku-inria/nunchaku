
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Rename values in a model} *)

open Nunchaku_core

module T = TermInner.Default

val name : string

val rename : (T.t, T.t) Model.t -> (T.t, T.t) Model.t
(** [rename m] performs a renaming of domain constants and bound variables
      that should be regular and readable.
      Assumes the types that have finite domains are ground types.
      @raise Invalid_argument if some assumption is invalidated *)

val pipe_rename :
  print:bool ->
  ('a, 'a, (T.t, T.t) Problem.Res.t, (T.t, T.t) Problem.Res.t) Transform.t
