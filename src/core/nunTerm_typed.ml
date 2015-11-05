
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

type 't repr = {
  repr: ('t, invariant) NunTerm_intf.repr;
  ty: 't -> 't option;
  loc: 't -> loc option;
}

type 't build = {
  b_repr: 't repr;
  b_build: ?loc:loc -> ty:'t -> ('t, invariant) view -> 't;
  b_kind: 't;
}
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

let view ~repr t = repr.repr t
let loc ~repr t = repr.loc t
let ty ~repr t = repr.ty t
let ty_exn ~repr t = match repr.ty t with
  | None -> raise Not_found
  | Some t -> t

let build ~build ?loc ~ty v = build.b_build ?loc ~ty v

(* special constants: kind and type *)
let kind_ ~build = build.b_kind

let ty_type ~build =
  build.b_build ?loc:None ~ty:build.b_kind (TI.TyBuiltin NunBuiltin.Ty.Type)

let ty_prop ~build =
  build.b_build ?loc:None ~ty:(ty_type ~build) (TI.TyBuiltin NunBuiltin.Ty.Prop)

let app_builtin ~build ?loc ~ty s l =
  build.b_build ?loc ~ty (TI.AppBuiltin (s,l))

let builtin ~build ?loc ~ty s = app_builtin ~build ?loc ~ty s []

let const ~build ?loc ~ty id =
  build.b_build ?loc ~ty (TI.Const id)

let var ~build ?loc v = build.b_build ?loc ~ty:(Var.ty v) (TI.Var v)

let app ~build ?loc ~ty t l =
  build.b_build ?loc ~ty (TI.App(t,l))

let mk_bind ~build ?loc ~ty b v t = build.b_build ?loc ~ty (TI.Bind (b,v,t))

let fun_ ~build ?loc ~ty v t = build.b_build ?loc ~ty (TI.Bind(TI.Fun,v, t))

let let_ ~build ?loc v t u =
  build.b_build ?loc ~ty:(ty_exn ~repr:build.b_repr u) (TI.Let (v, t, u))

let match_with ~build ?loc ~ty t l =
  if ID.Map.is_empty l then invalid_arg "Term_typed.case: no cases";
  build.b_build ?loc ~ty (TI.Match (t, l))

let ite ~build ?loc a b c =
  build.b_build?loc ~ty:(ty_exn ~repr:build.b_repr b)
    (TI.AppBuiltin (NunBuiltin.T.Ite, [a;b;c]))

let forall ~build ?loc v t =
  mk_bind ~build ?loc ~ty:(ty_prop ~build) TI.Forall v t

let exists ~build ?loc v t =
  mk_bind ~build ?loc ~ty:(ty_prop ~build) TI.Exists v t

let eq ~build ?loc a b =
  app_builtin ~build ?loc ~ty:(ty_prop ~build) NunBuiltin.T.Eq [a;b]

let ty_builtin ~build ?loc b =
  build.b_build ?loc ~ty:(ty_type ~build) (TI.TyBuiltin b)

let ty_const ~build ?loc id =
  const ~build ?loc ~ty:(ty_type ~build) id

let ty_var ~build ?loc v = var ~build ?loc v

let ty_meta_var ~build ?loc v = build.b_build ?loc ~ty:(ty_type ~build) (TI.TyMeta v)

let ty_app ~build ?loc f l = app ~build ?loc ~ty:(ty_type ~build) f l

let ty_arrow ~build ?loc a b =
  build.b_build ?loc ~ty:(ty_type ~build) (TI.TyArrow (a,b))

let ty_forall ~build ?loc a b =
  mk_bind ~build ?loc ~ty:(ty_type ~build) TI.TyForall a b

(* representation as a type *)
let as_ty ~repr : (_,invariant) TyI.repr
= fun t -> match repr.repr t with
  | TI.TyBuiltin b -> TyI.Builtin b
  | TI.Const id -> TyI.Const id
  | TI.Var v -> TyI.Var v
  | TI.App (f,l) -> TyI.App (f,l)
  | TI.TyArrow (a,b) -> TyI.Arrow (a,b)
  | TI.Bind(TI.TyForall,v,t) -> TyI.Forall (v,t)
  | TI.TyMeta v -> TyI.Meta v
  | TI.AppBuiltin _
  | TI.Bind _ | TI.Let _ | TI.Match _ -> assert false

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

let is_ty ~repr t = TyI.is_Type ~repr:(as_ty ~repr) (ty_exn ~repr t)

type default = {
  view : (default,invariant) view;
  d_loc : Loc.t option;
  mutable d_ty : default option;
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

let default_repr = {
  repr=(fun t -> (deref_rec_ t).view);
  loc=(fun t -> t.d_loc);
  ty=(fun t -> t.d_ty);
}

let make_raw_ ~loc ~ty view = { view; d_loc=loc; d_ty=Some ty; }

let b_build ?loc ~ty view = match view with
  | TI.App ({view=TI.App (f, l1); d_loc=loc; _}, l2) ->
      make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
  | TI.App ({view=TI.AppBuiltin (b, l1); d_loc=loc; _}, l2) ->
      make_raw_ ~loc ~ty (TI.AppBuiltin (b, l1@l2))
  | _ -> make_raw_ ~loc ~ty view

let default_build : default build = {
  b_repr = default_repr;
  b_build;
  b_kind={view=TI.TyBuiltin NunBuiltin.Ty.Kind; d_loc=None; d_ty=None; }
}

let as_ho ~repr : ('t, invariant) NunTerm_ho.repr =
  let fail_ () = failwith "Term_typed.as_ho: remaining meta" in
  let view t = match repr.repr t with
    | TI.TyMeta _ -> fail_ ()
    | TI.Const _
    | TI.Var _
    | TI.App (_,_)
    | TI.AppBuiltin (_,_)
    | TI.Bind (_,_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) as v -> v
  in
  view

let default_print =
  NunTerm_ho.mk_print ~repr:(as_ho ~repr:default_repr)
