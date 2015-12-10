
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

let pp out p =
  CCFormat.string out
    (match p with
    | Pos -> "+"
    | Neg -> "-"
    | NoPol -> "<none>")

