
(* This file is free software, part of nunchaku. See file "license" for more details. *)

type t =
  | Prop
  | Type
  | Not
  | And
  | Or
  | True
  | False
  | Imply
  | Equiv

let equal a b = a==b
let compare = Pervasives.compare
let hash = Hashtbl.hash

let prop = Prop
let type_ = Type
let not_ = Not
let and_ = And
let or_ = Or
let true_ = True
let false_ = False
let imply = Imply
let equiv = Equiv

let fixity = function
  | Type
  | True
  | False
  | Prop
  | Not -> `Prefix
  | And
  | Or
  | Imply
  | Equiv -> `Infix

let print out s =
  Format.pp_print_string out
    (match s with
    | Type -> "type"
    | Prop -> "prop"
    | Not -> "~"
    | And -> "&"
    | Or -> "|"
    | True -> "true"
    | False -> "false"
    | Imply -> "==>"
    | Equiv -> "<=>"
    )

let to_string = CCFormat.to_string print
