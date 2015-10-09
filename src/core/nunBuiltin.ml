
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
  let fixity = function
    | True
    | False
    | Not -> `Prefix
    | Or
    | And
    | Imply -> `Infix
  let to_string = function
    | True -> "true"
    | False -> "false"
    | Not -> "~"
    | Or -> "|"
    | And -> "&"
    | Imply -> "=>"
  let equal = (==)
end
