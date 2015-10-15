
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtin Symbols} *)

module Ty = struct
  type t =
    | Kind
    | Type
    | Prop
  let equal = (==)
  let to_string = function
    | Prop -> "prop"
    | Kind -> "kind"
    | Type -> "type"
end

module T = struct
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Ite
    | Eq
  let fixity = function
    | True
    | False
    | Ite
    | Not -> `Prefix
    | Eq
    | Or
    | And
    | Imply -> `Infix
  let to_string = function
    | True -> "true"
    | False -> "false"
    | Not -> "~"
    | Or -> "||"
    | And -> "&&"
    | Imply -> "=>"
    | Eq -> "="
    | Ite -> assert false
  let equal = (==)
end
