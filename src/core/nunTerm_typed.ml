
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

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

open NunTerm_intf

(** {2 Read-Only View} *)
module type VIEW = sig
  type invariant =
    <meta:NunMark.with_meta; poly: NunMark.polymorph>

  type t
  type ty = t
  val view : t -> (t, invariant) view

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : sig
    type ty = t
    val view : t -> (t,invariant) NunType_intf.view
  end
end

(** {2 Full Signature} *)
module type S = sig
  type invariant =
    <meta:NunMark.with_meta; poly: NunMark.polymorph>

  type t
  type ty = t

  val view : t -> (t, invariant) view

  val ty : t -> ty option
  (** The type of a term *)

  module Ty : sig
    include NunType_intf.AS_TERM
      with type term = t and type t = ty
      and type invariant_poly = NunMark.polymorph
      and type invariant_meta = NunMark.with_meta
    include NunIntf.PRINT with type t := t
    type ty = t

    val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  end

  val loc : t -> loc option

  val const : ?loc:loc -> ty:Ty.t -> id -> t
  val builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t
  val app_builtin : ?loc:loc -> ty:Ty.t -> NunBuiltin.T.t -> t list -> t
  val var : ?loc:loc -> Ty.t var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> ty var -> t -> t
  val let_ : ?loc:loc -> ty var -> t -> t -> t
  val match_with : ?loc:loc -> ty:Ty.t -> t -> ty NunTerm_intf.cases -> t
  val ite : ?loc:loc -> t -> t -> t -> t
  val forall : ?loc:loc -> ty var -> t -> t
  val exists : ?loc:loc -> ty var -> t -> t
  val eq : ?loc:loc -> t -> t -> t

  val mk_bind :
    ?loc:loc ->
    ty:Ty.t ->
    NunMark.polymorph NunTerm_intf.binder ->
    Ty.t var ->
    t ->
    t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunBuiltin.Ty.t -> Ty.t
  val ty_const : ?loc:loc -> id -> Ty.t
  val ty_var : ?loc:loc -> ty var -> Ty.t
  val ty_meta_var : ?loc:loc -> Ty.t NunMetaVar.t -> Ty.t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> ty var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

(** {2 Default Instance} *)
module Default = struct
  type invariant =
    <meta:NunMark.with_meta; poly: NunMark.polymorph>

  type t = {
    view : (t,invariant) view;
    loc : Loc.t option;
    mutable ty : t option;
  }

  (* dereference the term, if it is a variable, until it is not bound *)
  let rec deref_rec_ (t:t) = match t.view with
    | TyMeta var ->
        begin match MetaVar.deref var with
        | None -> t
        | Some t' ->
            let root = deref_rec_ t' in
            (* path compression *)
            if t' != root then MetaVar.rebind ~var root;
            root
        end
    | _ -> t

  let view t = (deref_rec_ t).view

  let loc t = t.loc

  let ty t = t.ty

  (* special constants: kind and type *)
  let kind_ = {view=TyBuiltin NunBuiltin.Ty.Kind; loc=None; ty=None}
  let type_ = {view=TyBuiltin NunBuiltin.Ty.Type; loc=None; ty=Some kind_}
  let prop = {view=TyBuiltin NunBuiltin.Ty.Prop; loc=None; ty=Some type_}

  let make_raw_ ~loc ~ty view = { view; loc; ty}

  let make_ ?loc ?ty view = match view with
    | App ({view=App (f, l1); loc; _}, l2) ->
        make_raw_ ~loc ~ty (App (f, l1 @ l2))
    | _ -> make_raw_ ~loc ~ty view

  let app_builtin ?loc ~ty s l = make_ ?loc ~ty (AppBuiltin (s,l))
  let builtin ?loc ~ty s = app_builtin ?loc ~ty s []
  let const ?loc ~ty id = make_ ?loc ~ty (Const id)
  let var ?loc v = make_ ?loc ~ty:(Var.ty v) (Var v)
  let app ?loc ~ty t l = match (deref_rec_ t).view, l with
    | _, [] -> t
    | AppBuiltin (b, l1), _ -> app_builtin ?loc ~ty b (l1@l)
    | _ ->  make_ ?loc ~ty (App (t, l))
  let mk_bind ?loc ~ty b v t = make_ ?loc ~ty (Bind (b,v,t))
  let fun_ ?loc ~ty v t = make_ ?loc ~ty (Bind(Fun,v, t))
  let let_ ?loc v t u = make_ ?loc ?ty:u.ty (Let (v, t, u))
  let match_with ?loc ~ty t l =
    if ID.Map.is_empty l then invalid_arg "Term_typed.case: no cases";
    make_ ?loc ~ty (Match (t, l))
  let ite ?loc a b c = make_ ?loc ?ty:b.ty (AppBuiltin (NunBuiltin.T.Ite, [a;b;c]))
  let forall ?loc v t = mk_bind ?loc ~ty:prop Forall v t
  let exists ?loc v t = mk_bind ?loc ~ty:prop Exists v t
  let eq ?loc a b = app_builtin ?loc ~ty:prop NunBuiltin.T.Eq [a;b]

  let ty_type = type_
  let ty_prop = prop

  let ty_builtin ?loc b = make_ ?loc ~ty:type_ (TyBuiltin b)
  let ty_const ?loc id = const ?loc ~ty:type_ id
  let ty_var ?loc v = var ?loc v
  let ty_meta_var ?loc v = make_ ?loc ~ty:type_ (TyMeta v)
  let ty_app ?loc f l =
    if l=[] then f else app ?loc ~ty:type_ f l
  let ty_arrow ?loc a b = make_ ?loc ~ty:type_ (TyArrow (a,b))
  let ty_forall ?loc a b = mk_bind ?loc ~ty:type_ TyForall a b

  module Ty1 = struct
    type invariant_poly = M.polymorph
    type invariant_meta = M.with_meta
    type invariant = <meta: invariant_meta; poly: invariant_poly>
    type term = t

    let view t = match (deref_rec_ t).view with
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | Var v -> TyI.Var v
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | Bind(TyForall,v,t) -> TyI.Forall (v,t)
      | TyMeta v -> TyI.Meta v
      | AppBuiltin _
      | Bind _ | Let _ | Match _ -> assert false
  end

  (* the real [Ty] module *)
  module Ty = struct
    include Ty1
    include TyI.Utils(struct include Ty1 type t = term end)
    type ty = t

    let is_ty t = match t.ty with
      | Some ty -> is_Type ty
      | _ -> false

    include TyI.Print(struct include Ty1 type t_ = t type t = t_ end)
  end

  include NunTerm_ho.Print(struct
    type invariant_poly = M.polymorph
    type invariant_meta = M.with_meta
    type invariant = <meta: invariant_meta; poly: invariant_poly>
    type ty = t
    type t = ty
    let view = view
    module Ty = struct include Ty1 type t = term end
  end)
end

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

let default = (module Default : S with type t = Default.t)

module AsHO(T : VIEW)
:
  NunTerm_ho.VIEW
    with type invariant_poly = NunMark.polymorph
    and type invariant_meta = NunMark.without_meta
    and type t = T.t and type ty = T.t
= struct
  type t = T.t
  type ty = t

  type invariant_poly = M.polymorph
  type invariant_meta = M.without_meta
  type invariant = <meta: invariant_meta; poly: invariant_poly>

  let fail_ () = failwith "Term_typed.AsHO.view: remaining meta"

  let view (t:t):(t,invariant) view = match T.view t with
    | TyMeta _ -> fail_ ()
    | Const _
    | Var _
    | App (_,_)
    | AppBuiltin (_,_)
    | Bind (_,_,_)
    | Let (_,_,_)
    | Match (_,_)
    | TyBuiltin _
    | TyArrow (_,_) as v -> v

  module Ty = struct
    type t = ty

    let view (t:t):(t,invariant) TyI.view = match T.Ty.view t with
      | TyI.Meta _ -> fail_ ()
      | TyI.Builtin _
      | TyI.Const _
      | TyI.Var _
      | TyI.App (_,_)
      | TyI.Arrow (_,_)
      | TyI.Forall (_,_) as v -> v
  end
end

let as_ho =
  let module T = AsHO(Default) in
  (module T : NunTerm_ho.VIEW with type t = Default.t
  and type invariant_meta=NunMark.without_meta
  and type invariant_poly=NunMark.polymorph)
