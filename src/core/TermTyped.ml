
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

module TI = TermInner
module Loc = Location

(*$inject
  module TI = TermInner
  module U = Util(Default)
*)

type 'a view = 'a TI.view
(** Same view as {!TermInner} *)

type loc = Loc.t
type id = ID.t
type 'a var = 'a Var.t

module type REPR = sig
  type t
  val repr : t -> t view
  val ty: t -> t option
  val loc: t -> loc option
end

module type BUILD = sig
  type t
  val build : ?loc:loc -> ty:t -> t view -> t
  val kind : t (* impossible to build otherwise *)
end

module type S = sig
  type t
  include REPR with type t := t
  include BUILD with type t := t
end

module LiftRepr(T : REPR) : TI.REPR with type t = T.t = struct
  type t = T.t
  let repr = T.repr
end

module Util(T : S)
  : sig
    type t = T.t

    val ty_exn : t -> t
    (** @raise Not_found if the term has no type *)

    val const : ?loc:loc -> ty:t -> id -> t
    val builtin : ?loc:loc -> ty:t -> t Builtin.t -> t
    val var : ?loc:loc -> t var -> t
    val app : ?loc:loc -> ty:t -> t -> t list -> t
    val fun_ : ?loc:loc -> ty:t -> t var -> t -> t
    val mu : ?loc:loc -> t var -> t -> t
    val let_ : ?loc:loc -> t var -> t -> t -> t
    val match_with : ?loc:loc -> ty:t -> t -> t TI.cases -> def:t TI.default_case -> t
    val ite : ?loc:loc -> t -> t -> t -> t
    val forall : ?loc:loc -> t var -> t -> t
    val exists : ?loc:loc -> t var -> t -> t
    val eq : ?loc:loc -> t -> t -> t
    val asserting : ?loc:loc -> t -> t list -> t
    val undefined_self : ?loc:loc -> t -> t

    val true_ : t
    val false_ : t

    val mk_bind :
      ?loc:loc ->
      ty:t ->
      Binder.t -> t var -> t -> t

    val ty_type : t (** Type of types *)
    val ty_prop : t (** Propositions *)
    val ty_unitype : t  (** $i in TPTP *)

    val ty_builtin : ?loc:loc -> TI.TyBuiltin.t -> t
    val ty_const : ?loc:loc -> id -> t
    val ty_app : ?loc:loc -> t -> t list -> t
    val ty_arrow : ?loc:loc -> t -> t -> t
    val ty_arrow_l : ?loc:loc -> t list -> t -> t

    val ty_var : ?loc:loc -> t var -> t
    val ty_forall : ?loc:loc -> t var -> t -> t

    val ty_meta_var : ?loc:loc -> t MetaVar.t -> t
    (** Meta-variable, ready for unif *)

    include TI.UTIL_REPR with type t_ := t

    val is_ty: t -> bool
    (** [is_ty t] same as [is_Type (type of t)] *)
  end = struct
  type t = T.t

  let build = T.build

  let ty_exn t = match T.ty t with
    | None -> raise Not_found
    | Some t -> t

  let ty_type =
    build ?loc:None ~ty:T.kind (TI.TyBuiltin `Type)

  let ty_prop =
    build ?loc:None ~ty:ty_type (TI.TyBuiltin `Prop)

  let ty_unitype =
    build ?loc:None ~ty:ty_type (TI.TyBuiltin `Unitype)

  let builtin ?loc ~ty b =
    build ?loc ~ty (TI.Builtin b)

  let const ?loc ~ty id =
    build ?loc ~ty (TI.Const id)

  let true_ = builtin ~ty:ty_prop `True
  let false_ = builtin ~ty:ty_prop `False

  let var ?loc v = build ?loc ~ty:(Var.ty v) (TI.Var v)

  let app ?loc ~ty t l =
    build ?loc ~ty (TI.App(t,l))

  let mk_bind ?loc ~ty b v t = build ?loc ~ty (TI.Bind (b,v,t))

  let fun_ ?loc ~ty v t = build ?loc ~ty (TI.Bind(Binder.Fun,v, t))

  let mu ?loc v t =
    (* typeof v = typeof t = typeof µv.t *)
    let ty = Var.ty v in
    build ?loc ~ty (TI.Bind (Binder.Mu, v, t))

  let let_ ?loc v t u =
    build ?loc ~ty:(ty_exn u) (TI.Let (v, t, u))

  let match_with ?loc ~ty t l ~def =
    if ID.Map.is_empty l then invalid_arg "Term_typed.case: no cases";
    build ?loc ~ty (TI.Match (t, l, def))

  let ite ?loc a b c =
    builtin ?loc ~ty:(ty_exn b) (`Ite (a,b,c))

  let forall ?loc v t =
    mk_bind ?loc ~ty:ty_prop Binder.Forall v t

  let exists ?loc v t =
    mk_bind ?loc ~ty:ty_prop Binder.Exists v t

  let eq ?loc a b =
    builtin ?loc ~ty:ty_prop (`Eq (a,b))

  let asserting ?loc t l = match l with
    | [] -> t
    | _::_ ->
      let g = { Builtin.asserting=l; } in
      builtin ?loc ~ty:(ty_exn t) (`Guard (t, g))

  let undefined_self ?loc t =
    builtin ?loc ~ty:(ty_exn t) (`Undefined_self t)

  let ty_builtin ?loc b =
    build ?loc ~ty:ty_type (TI.TyBuiltin b)

  let ty_const ?loc id =
    const ?loc ~ty:ty_type id

  let ty_var ?loc v = build ?loc ~ty:(Var.ty v) (TI.Var v)

  let ty_meta_var ?loc v = build ?loc ~ty:ty_type (TI.TyMeta v)

  let ty_app ?loc f l = app ?loc ~ty:ty_type f l

  let ty_arrow ?loc a b =
    build ?loc ~ty:ty_type (TI.TyArrow (a,b))
  let ty_arrow_l ?loc = List.fold_right (ty_arrow ?loc)

  let ty_forall ?loc a b =
    mk_bind ?loc ~ty:ty_type Binder.TyForall a b

  include TI.UtilRepr(LiftRepr(T))

  let is_ty t = ty_is_Type (ty_exn t)
end

(*$T
  U.ty_returns_Type U.ty_type
  U.ty_returns_Type U.(ty_arrow ty_prop ty_type)
  not (U.ty_returns_Type U.(ty_arrow ty_type ty_prop))
*)

module Default = struct
  type t = {
    view : t view;
    d_loc : Loc.t option;
    mutable d_ty : t option;
  }

  (* dereference the term, if it is a variable, until it is not bound;
     also does some simplifications *)
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
    | TI.App (f, []) -> f
    | TI.App ({view=TI.App (f, l1); d_loc=loc; _}, l2) ->
      make_raw_ ~loc ~ty (TI.App (f, l1 @ l2))
    | _ -> make_raw_ ~loc ~ty view

  let kind = {view=TI.TyBuiltin `Kind; d_loc=None; d_ty=None; }

  module Print = TI.Print(struct
      type t_ = t
      type t = t_
      let repr = repr
    end)
end
