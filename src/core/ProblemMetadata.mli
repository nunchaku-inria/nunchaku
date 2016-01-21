

(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Metadata attached to Problem} *)

type t = private {
  unsat_means_unknown: bool; (* we lost some models *)
  sat_means_unknown: bool; (* models may be spurious *)
}

val default: t

val set_unsat_means_unknown: t -> t
val add_unsat_means_unknown: bool -> t -> t

val set_sat_means_unknown: t -> t
val add_sat_means_unknown: bool -> t -> t
