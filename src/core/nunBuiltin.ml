
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtin Symbols} *)

module Ty = struct
  type t =
    | Prop
  let equal = (==)
  let to_string = function
    | Prop -> "prop"
end

module T = struct
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
    | Eq
  let fixity = function
    | True
    | False
    | Not -> `Prefix
    | Eq
    | Or
    | And
    | Imply
    | Equiv -> `Infix
  let to_string = function
    | True -> "true"
    | False -> "false"
    | Not -> "~"
    | Or -> "|"
    | And -> "&"
    | Imply -> "=>"
    | Equiv -> "<=>"
    | Eq -> "="
  let equal = (==)
end
