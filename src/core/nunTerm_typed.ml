
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

module TI = NunTerm_intf
module TyI = NunType_intf

module Loc = NunLocation
module Var = NunVar
module MetaVar = NunMetaVar
module ID = NunID

(*$inject
  module Var = NunVar

*)

type loc = Loc.t
type id = NunID.t
type 'a var = 'a Var.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

type invariant = <meta:NunMark.with_meta; poly: NunMark.polymorph>


type 't repr = ('t, invariant) NunTerm_intf.repr

type 't build = ?loc:loc -> ty:'t -> ('t, invariant) view -> 't
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

module type REPR = sig
  type t
  val repr : t repr
  val ty: t -> t option
  val loc: t -> loc option
end

module type BUILD = sig
  type t
  val build : t build
  val kind : t (* impossible to build otherwise *)
end

module type S = sig
  type t
  include REPR with type t := t
  include BUILD with type t := t
end

module Util(T : S) = struct
  type t = T.t

  let view = T.repr
  let loc = T.loc
  let ty = T.ty
  let ty_exn t = match T.ty t with
    | None -> raise Not_found
    | Some t -> t

  let build = T.build

  (* special constants: kind and type *)
  let kind_ = T.kind

  let ty_type =
    build ?loc:None ~ty:T.kind (TI.TyBuiltin NunBuiltin.Ty.Type)

  let ty_prop =
    build ?loc:None ~ty:ty_type (TI.TyBuiltin NunBuiltin.Ty.Prop)

  let app_builtin ?loc ~ty s l =
    build ?loc ~ty (TI.AppBuiltin (s,l))

  let builtin ?loc ~ty s = app_builtin ?loc ~ty s []

  let const ?loc ~ty id =
    build ?loc ~ty (TI.Const id)

  let var ?loc v = build ?loc ~ty:(Var.ty v) (TI.Var v)

  let app ?loc ~ty t l =
    build ?loc ~ty (TI.App(t,l))

  let mk_bind ?loc ~ty b v t = build ?loc ~ty (TI.Bind (b,v,t))

  let fun_ ?loc ~ty v t = build ?loc ~ty (TI.Bind(TI.Fun,v, t))

  let let_ ?loc v t u =
    build ?loc ~ty:(ty_exn u) (TI.Let (v, t, u))

  let match_with ?loc ~ty t l =
    if ID.Map.is_empty l then invalid_arg "Term_typed.case: no cases";
    build ?loc ~ty (TI.Match (t, l))

  let ite ?loc a b c =
    build?loc ~ty:(ty_exn b)
      (TI.AppBuiltin (NunBuiltin.T.Ite, [a;b;c]))

  let forall ?loc v t =
    mk_bind ?loc ~ty:ty_prop TI.Forall v t

  let exists ?loc v t =
    mk_bind ?loc ~ty:ty_prop TI.Exists v t

  let eq ?loc a b =
    app_builtin ?loc ~ty:ty_prop NunBuiltin.T.Eq [a;b]

  let ty_builtin ?loc b =
    build ?loc ~ty:ty_type (TI.TyBuiltin b)

  let ty_const ?loc id =
    const ?loc ~ty:ty_type id

  let ty_var ?loc v = var ?loc v

  let ty_meta_var ?loc v = build ?loc ~ty:ty_type (TI.TyMeta v)

  let ty_app ?loc f l = app ?loc ~ty:ty_type f l

  let ty_arrow ?loc a b =
    build ?loc ~ty:ty_type (TI.TyArrow (a,b))

  let ty_forall ?loc a b =
    mk_bind ?loc ~ty:ty_type TI.TyForall a b

  (* representation as a type *)
  let as_ty : (t,invariant) TyI.repr
  = fun t -> match view t with
    | TI.TyBuiltin b -> TyI.Builtin b
    | TI.Const id -> TyI.Const id
    | TI.TyVar v -> TyI.Var v
    | TI.App (f,l) -> TyI.App (f,l)
    | TI.TyArrow (a,b) -> TyI.Arrow (a,b)
    | TI.Bind(TI.TyForall,v,t) -> TyI.Forall (v,t)
    | TI.TyMeta v -> TyI.Meta v
    | TI.AppBuiltin _ | TI.Var _
    | TI.Bind _ | TI.Let _ | TI.Match _ -> assert false

  let is_ty t = TyI.is_Type ~repr:as_ty (ty_exn t)
end

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

let as_ho ~repr : ('t, invariant) NunTerm_ho.repr =
  let fail_ () = failwith "Term_typed.as_ho: remaining meta" in
  let view t = match repr t with
    | TI.TyMeta _ -> fail_ ()
    | TI.Const _
    | TI.Var _
    | TI.TyVar _
    | TI.App (_,_)
    | TI.AppBuiltin (_,_)
    | TI.Bind (_,_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) as v -> v
  in
  view

module Default = struct
  type t = {
    view : (t,invariant) view;
    d_loc : Loc.t option;
    mutable d_ty : t option;
  }

  (* dereference the term, if it is a variable, until it is not bound *)
  let rec deref_rec_ t = match t.view with
    | TI.TyMeta var ->
        begin match MetaVar.deref var with
        | None -> t
        | Some t' ->
            let root = deref_rec_ t' in
            (* path compression *)
            if t' != root then MetaVar.rebind ~var root;
            root
        end
    | _ -> t

  let repr t = (deref_rec_ t).view
  let loc t = t.d_loc
  let ty t = t.d_ty

  let make_raw_ ~loc ~ty view = { view; d_loc=loc; d_ty=Some ty; }

  let build ?loc ~ty view = match view with
    | TI.App ({view=TI.App (f, l1); d_loc=loc; _}, l2) ->
        make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
    | TI.App ({view=TI.AppBuiltin (b, l1); d_loc=loc; _}, l2) ->
        make_raw_ ~loc ~ty (TI.AppBuiltin (b, l1@l2))
    | _ -> make_raw_ ~loc ~ty view

  let kind = {view=TI.TyBuiltin NunBuiltin.Ty.Kind; d_loc=None; d_ty=None; }

let print_funs = NunTerm_ho.mk_print ~repr:(as_ho ~repr)
end
