
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
  module TyI = NunType_intf
  module U = Util(Default)

*)

type loc = Loc.t
type id = NunID.t
type 'a var = 'a Var.t

type ('a,'inv) view = ('a,'inv) NunTerm_intf.view

type ('t,'inv) repr = ('t, 'inv) NunTerm_intf.repr

type ('t,'inv) build = ?loc:loc -> ty:'t -> ('t, 'inv) view -> 't
(** Builder is specific: we also need the type of the term, and an
    optional location. *)

module type REPR = sig
  type 'i t
  val repr : ('i t,'i) repr
  val ty: 'i t -> 'i t option
  val loc: _ t -> loc option
end

module type BUILD = sig
  type 'i t
  val build : ('i t, 'i) build
  val kind : unit -> 'i t (* impossible to build otherwise *)
end

module type S = sig
  type 'i t
  include REPR with type 'i t := 'i t
  include BUILD with type 'i t := 'i t
end

module Util(T : S) = struct
  type 'i t = 'i T.t

  let view = T.repr
  let loc = T.loc
  let ty = T.ty
  let ty_exn t = match T.ty t with
    | None -> raise Not_found
    | Some t -> t

  let build = T.build

  let ty_type() =
    build ?loc:None ~ty:(T.kind ()) (TI.TyBuiltin NunBuiltin.Ty.Type)

  let ty_prop() =
    build ?loc:None ~ty:(ty_type ()) (TI.TyBuiltin NunBuiltin.Ty.Prop)

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
    mk_bind ?loc ~ty:(ty_prop ()) TI.Forall v t

  let exists ?loc v t =
    mk_bind ?loc ~ty:(ty_prop ()) TI.Exists v t

  let eq ?loc a b =
    app_builtin ?loc ~ty:(ty_prop ()) NunBuiltin.T.Eq [a;b]

  let ty_builtin ?loc b =
    build ?loc ~ty:(ty_type()) (TI.TyBuiltin b)

  let ty_const ?loc id =
    const ?loc ~ty:(ty_type()) id

  let ty_var ?loc v = build ?loc ~ty:(Var.ty v) (TI.TyVar v)

  let ty_meta_var ?loc v = build ?loc ~ty:(ty_type()) (TI.TyMeta v)

  let ty_app ?loc f l = app ?loc ~ty:(ty_type()) f l

  let ty_arrow ?loc a b =
    build ?loc ~ty:(ty_type()) (TI.TyArrow (a,b))

  let ty_forall ?loc a b =
    mk_bind ?loc ~ty:(ty_type()) TI.TyForall a b

  (* representation as a type *)
  let as_ty : type inv. (inv t,inv) TyI.repr
  = fun t -> match view t with
    | TI.TyBuiltin b -> TyI.Builtin b
    | TI.Const id -> TyI.Const id
    | TI.TyVar v -> TyI.Var v
    | TI.App (f,l) -> TyI.App (f,l)
    | TI.TyArrow (a,b) -> TyI.Arrow (a,b)
    | TI.Bind(TI.TyForall,v,t) -> TyI.Forall (v,t)
    | TI.TyMeta v -> TyI.Meta v
    | TI.AppBuiltin _ | TI.Var _ | TI.Let _ | TI.Match _ -> assert false
    | TI.Bind _ -> assert false

  let is_ty t = TyI.is_Type ~repr:as_ty (ty_exn t)
end

(*$T
  TyI.returns_Type ~repr:U.as_ty (U.ty_type())
  TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_prop()) (ty_type()))
  not (TyI.returns_Type ~repr:U.as_ty U.(ty_arrow (ty_type()) (ty_prop())))
*)

module AsHO(T : REPR) : NunTerm_ho.REPR with type 'a t = 'a T.t = struct
  type 'a t = 'a T.t

  let fail_ () = failwith "Term_typed.as_ho: remaining meta"

  let repr : type inv. (inv T.t, inv) NunTerm_ho.repr
  = fun t -> match T.repr t with
      | TI.TyMeta _ -> fail_ ()
      | TI.TyVar v -> TI.TyVar v
      | TI.Const _
      | TI.Var _
      | TI.App (_,_)
      | TI.AppBuiltin (_,_)
      | TI.Let (_,_,_)
      | TI.Match (_,_)
      | TI.TyBuiltin _
      | TI.TyArrow (_,_) as v -> v
      | TI.Bind (_,_,_) as v -> v
end

module Default = struct
  type 'i t = {
    view : ('i t,'i) view;
    d_loc : Loc.t option;
    mutable d_ty : 'i t option;
  }

  (* dereference the term, if it is a variable, until it is not bound;
   also does some simplifications *)
  let rec deref_rec_
  : type inv. inv t -> inv t
  = fun t -> match t.view with
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
    | TI.App (f, []) -> f
    | TI.App ({view=TI.App (f, l1); d_loc=loc; _}, l2) ->
        make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
    | TI.App ({view=TI.AppBuiltin (b, l1); d_loc=loc; _}, l2) ->
        make_raw_ ~loc ~ty (TI.AppBuiltin (b, l1@l2))
    | _ -> make_raw_ ~loc ~ty view

  let kind () = {view=TI.TyBuiltin NunBuiltin.Ty.Kind; d_loc=None; d_ty=None; }

  let print_funs () =
    let module R = AsHO(struct
      type 'a t_ = 'a t
      type 'a t = 'a t_
      let repr = repr
      let ty = ty
      let loc = loc
    end) in
    NunTerm_ho.mk_print ~repr:R.repr
end
