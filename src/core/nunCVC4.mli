
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module Make(FO : NunFO.VIEW) : sig
  include NunSolver_intf.S with module FO = FO

  val print_problem : Format.formatter -> problem -> unit
end
