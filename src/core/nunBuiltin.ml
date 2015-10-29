
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtin Symbols} *)

module ID = NunID

type id = ID.t

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
    | Equiv
    | Ite
    | Eq
    | DataTest of id (** Test whether [t : tau] starts with given constructor *)
    | DataSelect of id * int (** Select n-th argument of given constructor *)

  let fixity = function
    | True
    | False
    | Ite
    | Not
    | DataSelect _
    | DataTest _ -> `Prefix
    | Eq
    | Or
    | And
    | Equiv
    | Imply -> `Infix

  let to_string = function
    | True -> "true"
    | False -> "false"
    | Not -> "~"
    | Or -> "||"
    | And -> "&&"
    | Imply -> "=>"
    | Equiv
    | Eq -> "="
    | DataTest id -> "is-" ^ ID.name id
    | DataSelect (id, n) -> CCFormat.sprintf "select-%s-%d" (ID.name id) n
    | Ite -> assert false

  let equal a b = match a, b with
    | True, True
    | False, False
    | Not, Not
    | Or, Or
    | And, And
    | Imply, Imply
    | Equiv, Equiv
    | Ite, Ite
    | Eq, Eq -> true
    | DataTest id, DataTest id' -> ID.equal id id'
    | DataSelect (id, n), DataSelect (id', n') -> n=n' && ID.equal id id'
    | True, _
    | False, _
    | Ite, _
    | Not, _
    | Eq, _
    | Or, _
    | And, _
    | Equiv, _
    | Imply, _
    | DataSelect _, _
    | DataTest _, _ -> false
end
