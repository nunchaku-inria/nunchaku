
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = NunTerm_intf
module TyI = NunType_intf

module Loc = NunLocation
module Var = NunVar

(*$inject
  module Var = NunVar

*)

(** {1 Terms with Types} *)

type t = {
  view : (t,t) TI.view;
  loc : Loc.t option;
  mutable ty : t option;
}

(* dereference the term, if it is a variable, until it is not bound *)
let rec deref_rec_ t = match t.view with
  | TI.TyMeta (_, ({NunDeref.deref=Some t'; _} as ref)) ->
      let root = deref_rec_ t' in
      (* path compression *)
      if t' != root then NunDeref.rebind ~ref root;
      root
  | _ -> t

let view t = (deref_rec_ t).view

let loc t = t.loc

let ty t = t.ty

(* special constants: kind and type *)
let kind_ = {view=TI.TyKind; loc=None; ty=None}
let type_ = {view=TI.TyType; loc=None; ty=Some kind_}
let prop = {view=TI.TyBuiltin TyI.Builtin.Prop; loc=None; ty=Some type_}

let make_raw_ ~loc ~ty view = { view; loc; ty}

let make_ ?loc ?ty view = match view with
  | TI.App ({view=TI.App (f, l1); loc; _}, l2) ->
      make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
  | _ -> make_raw_ ~loc ~ty view

let build t = make_ t

let builtin ?loc ~ty s = make_ ?loc ~ty (TI.Builtin s)
let var ?loc ~ty v = make_ ?loc ~ty (TI.Var v)
let app ?loc ~ty t l =
  if l=[] then t else make_ ?loc ~ty (TI.App (t, l))
let fun_ ?loc ~ty v ~ty_arg t = make_ ?loc ~ty (TI.Fun (v, ty_arg, t))
let let_ ?loc v t u = make_ ?loc ?ty:u.ty (TI.Let (v, t, u))
let forall ?loc v ~ty_arg t = make_ ?loc ~ty:prop (TI.Forall (v, ty_arg, t))
let exists ?loc v ~ty_arg t = make_ ?loc ~ty:prop (TI.Exists (v, ty_arg, t))

let ty_type = type_
let ty_prop = prop

let ty_builtin ?loc b = make_ ?loc ~ty:type_ (TI.TyBuiltin b)
let ty_var ?loc v = var ?loc ~ty:type_ v
let ty_meta_var ?loc v = make_ ?loc (TI.TyMeta (v, NunDeref.create()))
let ty_app ?loc f l =
  if l=[] then f else app ?loc ~ty:type_ f l
let ty_arrow ?loc a b = make_ ?loc ~ty:type_ (TI.TyArrow (a,b))
let ty_forall ?loc a b = make_ ?loc ~ty:type_ (TI.TyForall(a,b))

module Ty = struct
  type term = t

  type t = term

  let is_Type t = match (deref_rec_ t).view with
    | TI.TyType -> true
    | _ -> false

  let is_Kind t = match (deref_rec_ t).view with
    | TI.TyKind -> true
    | _ -> false

  let rec returns_Type t = match (deref_rec_ t).view with
    | TI.TyType -> true
    | TI.TyArrow (_, t')
    | TI.TyForall (_, t') -> returns_Type t'
    | _ -> false

  let to_term t = t

  let is_ty t = match t.ty with
    | Some ty -> is_Type ty
    | _ -> false

  let of_term t =
    if is_ty t then Some t else None

  let of_term_exn t =
    if is_ty t then t else failwith "Term_mut.TyI.of_term_exn"

  let view t = match (deref_rec_ t).view with
    | TI.TyKind -> TyI.Kind
    | TI.TyType -> TyI.Type
    | TI.TyBuiltin b -> TyI.Builtin b
    | TI.TyMeta (v, d) -> TyI.Meta (v,d)
    | TI.Var v -> TyI.Var v
    | TI.App (f,l) -> TyI.App (f,l)
    | TI.TyArrow (a,b) -> TyI.Arrow (a,b)
    | TI.TyForall (v,t) -> TyI.Forall (v,t)
    | TI.Builtin _
    | TI.Fun (_,_,_)
    | TI.Forall (_,_,_)
    | TI.Exists (_,_,_)
    | TI.Let (_,_,_) -> assert false

  let build = function
    | TyI.Kind -> kind_
    | TyI.Type -> type_
    | TyI.Builtin b -> ty_builtin b
    | TyI.Var v -> var ~ty:type_ v
    | TyI.Meta (v, d) -> make_ (TI.TyMeta(v,d))
    | TyI.App (f,l) -> app ~ty:type_ f l
    | TyI.Arrow (a,b) -> ty_arrow a b
    | TyI.Forall (v,t) -> ty_forall v t

  let fpf = Format.fprintf

  let rec print out ty = match view ty with
    | TyI.Kind -> CCFormat.string out "kind"
    | TyI.Type -> CCFormat.string out "type"
    | TyI.Builtin b -> CCFormat.string out (TyI.Builtin.to_string b)
    | TyI.Meta (v,_)
    | TyI.Var v -> Var.print out v
    | TyI.App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | TyI.Arrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_app a print_in_arrow b
    | TyI.Forall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print t
  and print_in_app out t = match view t with
    | TyI.Builtin _ | TyI.Kind | TyI.Type | TyI.Var _ | TyI.Meta _ -> print out t
    | TyI.App (_,_)
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match view t with
    | TyI.Builtin _ | TyI.Kind | TyI.Type | TyI.Var _ | TyI.Meta _
    | TyI.App (_,_) -> print out t
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> fpf out "@[(%a)@]" print t
end

