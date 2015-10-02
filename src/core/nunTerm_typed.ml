
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
  mutable deref : deref;  (** used only for type variables *)
  mutable ty : t option;
}
and deref =
  | Deref_none (** not a variable *)
  | Deref_meta (** variable ready for unif *)
  | Deref_to of t (** variable bound to some term *)

let view t = t.view

let loc t = t.loc

let ty t = t.ty

(* special constants: kind and type *)
let kind_ = {view=TI.TyKind; loc=None; ty=None; deref=Deref_none}
let type_ = {view=TI.TyType; loc=None; ty=Some kind_; deref=Deref_none}
let prop = {view=TI.TyBuiltin TyI.Builtin.Prop; loc=None; ty=Some type_; deref=Deref_none}

let make_raw_ ~loc ~ty view = { view; loc; ty; deref=Deref_none}

let make_ ?loc ?ty view = match view with
  | TI.App ({view=TI.App (f, l1); loc; _}, l2) ->
      make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
  | _ -> make_raw_ ~loc ~ty view

let build t = make_ t

let builtin ?loc ~ty s = make_ ?loc ~ty (TI.Builtin s)
let var ?loc ~ty v = make_ ?loc ~ty (TI.Var v)
let app ?loc ~ty t l = make_ ?loc ~ty (TI.App (t, l))
let fun_ ?loc ~ty v ~ty_arg t = make_ ?loc ~ty (TI.Fun (v, ty_arg, t))
let let_ ?loc v t u = make_ ?loc ?ty:u.ty (TI.Let (v, t, u))
let forall ?loc v ~ty_arg t = make_ ?loc ~ty:prop (TI.Forall (v, ty_arg, t))
let exists ?loc v ~ty_arg t = make_ ?loc ~ty:prop (TI.Exists (v, ty_arg, t))

let ty_type = type_
let ty_prop = prop

let ty_builtin ?loc b = make_ ?loc ~ty:type_ (TI.TyBuiltin b)
let ty_var ?loc v = var ?loc ~ty:type_ v
let ty_meta_var ?loc v = {view=TI.Var v; loc;ty=Some type_; deref=Deref_meta}
let ty_app ?loc f l = app ?loc ~ty:type_ f l
let ty_arrow ?loc a b = make_ ?loc ~ty:type_ (TI.TyArrow (a,b))
let ty_forall ?loc a b = make_ ?loc ~ty:type_ (TI.TyForall(a,b))

module Ty = struct
  type term = t

  type t = term

  let is_Type t = match t.view with
    | TI.TyType -> true
    | _ -> false

  let is_Kind t = match t.view with
    | TI.TyKind -> true
    | _ -> false

  let rec returns_Type t = match t.view with
    | TI.TyType -> true
    | TI.TyArrow (_, t)
    | TI.TyForall (_, t) -> returns_Type t
    | _ -> false

  let to_term t = t

  let is_ty t = match t.ty with
    | Some {view=TI.TyType; _} -> true
    | _ -> false

  let of_term t =
    if is_ty t then Some t else None

  let of_term_exn t =
    if is_ty t then t else failwith "Term_mut.TyI.of_term_exn"

  let view t = match t.view with
    | TI.TyKind -> TyI.Kind
    | TI.TyType -> TyI.Type
    | TI.TyBuiltin b -> TyI.Builtin b
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
    | TyI.App (f,l) -> app ~ty:type_ f l
    | TyI.Arrow (a,b) -> ty_arrow a b
    | TyI.Forall (v,t) -> ty_forall v t

  let rec fold fun_ t = match view t with
    | TyI.Kind -> fun_ TyI.Kind
    | TyI.Type -> fun_ TyI.Type
    | TyI.Var v -> fun_ (TyI.Var v)
    | TyI.Builtin b -> fun_ (TyI.Builtin b)
    | TyI.App (f,l) ->
        let f = fold fun_ f in
        let l = List.map (fold fun_) l in
        fun_ (TyI.App (f,l))
    | TyI.Arrow (a,b) -> fun_ (TyI.Arrow (fold fun_ a, fold fun_ b))
    | TyI.Forall (v,t) -> fun_ (TyI.Forall (v, fold fun_ t))

  let is_var t = match t.view with TI.Var _ -> true | _ -> false

  let can_bind t = is_var t && match t.deref with
    | Deref_meta -> true
    | Deref_none
    | Deref_to _ -> false

  (*$T
    Ty.can_bind (ty_meta_var (Var.make ~name:"foo"))
    not (Ty.can_bind (ty_var (Var.make ~name:"bar")))
  *)

  (*$R
    let v = ty_meta_var (Var.make ~name:"a") in
    let v2 = ty_var (Var.make ~name:"b") in
    Ty.bind v v2;
    assert_bool "cannot bind"
      (not (Ty.can_bind v))
  *)

  (* dereference the type, if it is a variable, until it is not bound *)
  let rec deref t = match t.deref with
    | Deref_meta
    | Deref_none -> None
    | Deref_to t' ->
        match deref t' with
        | None -> Some t' (* t' is root *)
        | Some root as res ->
            (* path compression *)
            t.deref <- Deref_to root;
            res

  let bind ~var t =
    if not (can_bind var) then invalid_arg "Type_mut.bind";
    var.deref <- Deref_to t

  let fpf = Format.fprintf

  let rec print out ty = match view ty with
    | TyI.Kind -> CCFormat.string out "kind"
    | TyI.Type -> CCFormat.string out "type"
    | TyI.Builtin b -> CCFormat.string out (TyI.Builtin.to_string b)
    | TyI.Var v -> Var.print out v
    | TyI.App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | TyI.Arrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_app a print_in_arrow b
    | TyI.Forall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print t
  and print_in_app out t = match view t with
    | TyI.Builtin _ | TyI.Kind | TyI.Type | TyI.Var _ -> print out t
    | TyI.App (_,_)
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match view t with
    | TyI.Builtin _ | TyI.Kind | TyI.Type | TyI.Var _
    | TyI.App (_,_) -> print out t
    | TyI.Arrow (_,_)
    | TyI.Forall (_,_) -> fpf out "@[(%a)@]" print t
end

