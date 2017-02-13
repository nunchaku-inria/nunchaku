
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Binders} *)

type t =
  | Forall
  | Exists
  | Fun
  | TyForall
  | Mu  (** fixpoint *)

let to_string : t -> string = function
  | Fun -> "fun"
  | Forall -> "forall"
  | Exists -> "exists"
  | TyForall -> "pi"
  | Mu -> "mu"

let pp out b = CCFormat.string out (to_string b)
