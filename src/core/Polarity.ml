
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarity} *)

type t =
  | Pos
  | Neg
  | NoPol

let inv = function
  | Pos -> Neg
  | Neg -> Pos
  | NoPol -> NoPol

let equal = (=)

let to_string = function
  | Pos -> "+"
  | Neg -> "-"
  | NoPol -> ""

let is_pos = function
  | Pos -> true
  | Neg | NoPol -> false

let is_neg = function
  | Neg -> true
  | Pos | NoPol -> false

let pp out p = CCFormat.string out (to_string p)

