
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types with polymorphism and meta-variables} *)

module ID = NunID
module Var = NunVar
module MetaVar = NunMetaVar
module TI = NunTermInner

module Builtin = TI.TyBuiltin

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

type 'a view =
  | Builtin of Builtin.t (** Builtin type *)
  | Const of id
  | Var of 'a var
  | Meta of 'a MetaVar.t
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of 'a var * 'a

type 't repr = 't -> 't view
(** A representation of types with concrete type ['t].
    The view function must follow {!deref} pointers *)

type 't build = 't view -> 't

module type REPR = sig
  type t
  val repr : t repr
end

module type BUILD = sig
  type t
  val build : t build
end

module type S = sig
  module INNER : TI.S
  type t = private INNER.t
  include REPR with type t := t
  include BUILD with type t := t

  val of_inner_unsafe : INNER.t -> t
  (** Careful, this is totally unsafe and will result in [assert false] at
    some point if not properly used *)
end

module MakeRepr(T : TI.REPR)
: REPR with type t = T.t
= struct
  type t = T.t

  let repr t = match T.repr t with
    | TI.TyBuiltin b -> Builtin b
    | TI.Const id -> Const id
    | TI.App (f,l) -> App (f,l)
    | TI.TyArrow (a,b) -> Arrow (a,b)
    | TI.Var v -> Var v
    | TI.Bind (`TyForall, v, t) -> Forall (v,t)
    | TI.TyMeta v -> Meta v
    | TI.AppBuiltin _
    | TI.Match _
    | TI.Let _ -> assert false
    | TI.Bind _ -> assert false
end

module Make(T : TI.S)
: sig
  include S with module INNER = T

  include TI.PRINT with type t := t
end = struct
  module INNER = T
  module R = MakeRepr(T)

  type t = T.t

  let repr = R.repr

  let build v = T.build
    (match v with
    | Var v -> TI.Var v
    | Builtin b -> TI.TyBuiltin b
    | Const id -> TI.Const id
    | Meta v -> TI.TyMeta v
    | App (f,l) -> TI.App (f,l)
    | Arrow (a,b) -> TI.TyArrow(a,b)
    | Forall (v,t) -> TI.Bind (`TyForall,v,t)
    )

  include (TI.Print(INNER) : TI.PRINT with type t := t)

  let of_inner_unsafe t = t
end

