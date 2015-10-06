
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

include NunSolver_intf.S

val print_problem : Format.formatter -> NunSolver_intf.Problem.t -> unit
