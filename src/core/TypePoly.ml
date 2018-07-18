
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types with polymorphism and meta-variables} *)

module TI = TermInner

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

(** A polymorphic type is a term that respects {!is_ty} *)
module type S = sig
  module T : TI.REPR

  val is_ty : T.t -> bool

  val repr : T.t -> T.t view
  (** Present a type-centric view of a term.
      @raise Assert_failure if the term isn't a proper type, that
        is, if [is_ty t = false] *)
end

module Make(T : TI.REPR)
  : S with module T = T
= struct
  module T = T

  let rec is_ty t = match T.repr t with
    | TI.TyBuiltin _
    | TI.Const _ -> true
    | TI.App (f,l) -> is_ty f && List.for_all is_ty l
    | TI.TyArrow (a,b) -> is_ty a && is_ty b
    | TI.Var v -> is_ty_var v
    | TI.Bind (Binder.TyForall, v, t) -> is_ty_var v && is_ty t
    | TI.TyMeta _ -> true
    | TI.Builtin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> false
  and is_ty_var v = match T.repr (Var.ty v) with
    | TI.TyBuiltin `Type -> true
    | _ -> false

  let rec repr t = match T.repr t with
    | TI.TyBuiltin b -> Builtin b
    | TI.Const id -> Const id
    | TI.App (f,l) -> App (f, l)
    | TI.TyArrow (a, b) -> Arrow (a, b)
    | TI.Var v -> Var v
    | TI.Bind (Binder.TyForall, v, t) -> Forall (v, t)
    | TI.TyMeta {MetaVar.deref=Some u;_} -> repr u (* follow *)
    | TI.TyMeta v -> Meta v
    | TI.Builtin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> assert false
end

let default =
  let module M = Make(TI.Default) in
  (module M : S with type T.t = TI.Default.t)
