
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Pattern}

  A pattern is found on the left of a (nested) pattern match. It is built
  from constructors and variables only. *)

module TI = TermInner

type id = ID.t
type 'a var = 'a Var.t

type 'a view =
  | App of id * 'a list (* constructor application *)
  | Var of 'a var

module type S = sig
  module T : TI.REPR
  type t = T.t

  val repr : T.t -> T.t view
  (** View that fails on meta variables *)
end

module Make(T : TI.REPR)
: S with module T = T
= struct
  module T = T
  type t = T.t

  let repr t = match T.repr t with
    | TI.Const id -> App (id, [])
    | TI.Var v -> Var v
    | TI.App (f,l) ->
        begin match T.repr f with
        | TI.Const id -> App (id, l)
        | _ -> assert false
        end
    | TI.AppBuiltin _
    | TI.Bind _
    | TI.Let _
    | TI.Match _
    | TI.TyBuiltin _
    | TI.TyArrow _
    | TI.TyMeta _ -> assert false
end
