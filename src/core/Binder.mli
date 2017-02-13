
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Binders} *)

type t =
  | Forall
  | Exists
  | Fun
  | TyForall
  | Mu  (** fixpoint *)

val pp : t CCFormat.printer
val to_string : t -> string
