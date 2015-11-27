
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphic Types} *)

module ID = ID
module Var = Var
module MetaVar = MetaVar
module TI = TermInner
module Subst = Var.Subst

module Builtin = TI.TyBuiltin

type id = ID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

type 'a view =
  | Builtin of Builtin.t (** Builtin type *)
  | Const of id
  | App of 'a * 'a list
  | Arrow of 'a * 'a

(** A polymorphic type is a term that respects {!is_ty} *)
module type S = sig
  module T : TI.REPR

  val is_ty : T.t -> bool

  val repr : T.t -> T.t view

  val repr_with : subst:(T.t,T.t) Subst.t -> T.t -> T.t view
  (** representation that follows the substitution. Will
      fail on a variable, except if it is bound *)
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
    | TI.TyMeta _
    | TI.Var _
    | TI.AppBuiltin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> false

  let repr t = match T.repr t with
    | TI.TyBuiltin b -> Builtin b
    | TI.Const id -> Const id
    | TI.App (f,l) -> App (f, l)
    | TI.TyArrow (a, b) -> Arrow (a, b)
    | TI.Var _
    | TI.TyMeta _
    | TI.AppBuiltin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> assert false

  let rec repr_with ~subst t = match T.repr t with
    | TI.TyBuiltin b -> Builtin b
    | TI.Const id -> Const id
    | TI.App (f,l) -> App (f, l)
    | TI.TyArrow (a, b) -> Arrow (a, b)
    | TI.Var v ->
        begin match Subst.find ~subst v with
        | None -> assert false
        | Some t' -> repr_with ~subst t'
        end
    | TI.TyMeta _
    | TI.AppBuiltin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> assert false
end

let default =
  let module M = Make(TI.Default) in
  (module M : S with type T.t = TI.Default.t)
