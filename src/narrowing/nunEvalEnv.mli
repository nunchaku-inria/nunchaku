
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Global and Local Environment for Evaluation} *)

module T = NunTermEval

type id = NunID.t

type t

val create: unit -> t
val find_exn: env:t -> id -> T.const
val find: env:t -> id -> T.const option
val declare: env:t -> T.const -> t
