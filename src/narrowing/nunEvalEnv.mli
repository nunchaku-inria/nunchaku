
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Global and Local Environment for Evaluation} *)

module T = NunTermEval
module Const = NunEvalConst

type id = NunID.t

type t

val create: unit -> t
val find_exn: env:t -> id -> T.ty Const.t
val find: env:t -> id -> T.ty Const.t option
val declare: env:t -> T.ty Const.t -> t
