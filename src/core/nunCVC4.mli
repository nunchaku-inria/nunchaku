
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module CVC4 : NunSolver_intf.S

val solver : (module NunSolver_intf.S)
(** The solver interface to CVC4 *)
