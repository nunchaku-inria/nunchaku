
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Metadata attached to Problem} *)

type t = {
  unsat_means_unknown: bool; (* we lost some models *)
  sat_means_unknown: bool; (* models may be spurious *)
}

let default =
  { sat_means_unknown=false;
    unsat_means_unknown=false;
  }

let set_sat_means_unknown m = {m with sat_means_unknown=true; }
let add_sat_means_unknown b m = if b then set_sat_means_unknown m else m

let set_unsat_means_unknown m = {m with unsat_means_unknown=true; }
let add_unsat_means_unknown b m = if b then set_unsat_means_unknown m else m
