
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Printing Precedence}

    Order matters, as it defines priorities *)
type t =
  | Bot
  | App
  | Arrow
  | Eq
  | Not
  | Guard
  | Ite
  | Bind
  | And
  | Or
  | Top (* toplevel precedence *)
