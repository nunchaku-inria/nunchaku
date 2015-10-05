
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

module ID = NunID
module Var = NunVar
module TyI = NunType_intf

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]

module Builtin = NunTerm_typed.Builtin

type ('a, 'ty) view =
  | Builtin of Builtin.t (** built-in symbol *)
  | Const of id (** top-level symbol *)
  | Var of 'ty var (** bound variable *)
  | App of 'a * 'a list
  | Fun of 'ty var * 'a
  | Forall of 'ty var * 'a
  | Exists of 'ty var * 'a
  | Let of 'ty var * 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunType_intf.Builtin.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)

type ('t, 'ty) problem = {
  statements : ('t, 'ty) NunStatement.t list;
  signature : 'ty NunID.Map.t; (* id -> type *)
  defs : 't NunID.Map.t; (* id -> definition *)
}

module type VIEW = sig
  type t

  type ty = private t

  val view : t -> (t, ty) view
end

module type S = sig
  include VIEW

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty

    exception Error of string * t * t list
    (** Raised when a type application fails *)

    val apply : t -> t list -> t
    (** [apply t l] computes the type of [f args] where [f : t] and [args : l]
        @raise Error if the arguments do not match *)
  end

  val const : id -> t
  val builtin : Builtin.t -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunType_intf.Builtin.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_var : ty var -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t

  type signature = Ty.t NunID.Map.t

  val ty : sigma:signature -> t -> Ty.t or_error
  (** Compute the type of the given term in the given signature *)

  exception Undefined of id

  val ty_exn : sigma:signature -> t -> Ty.t
  (** @raise Ty.Error in case of error at an application
      @raise Undefined in case some symbol is not defined *)
end

module Default : S = struct
  type t = {
    view: (t, t) view;
  }

  type ty = t

  (* special constants: kind and type *)
  let kind_ = {view=TyKind}
  let type_ = {view=TyType}
  let prop = {view=TyBuiltin TyI.Builtin.Prop}

  let view t = t.view

  let make_raw_ view = { view}

  let make_ view = match view with
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  let builtin s = make_ (Builtin s)
  let const id = make_ (Const id)
  let var v = make_ (Var v)
  let app t l =
    if l=[] then t else make_ (App (t, l))
  let fun_ v t = make_ (Fun (v, t))
  let let_ v t u = make_ (Let (v, t, u))
  let forall v t = make_ (Forall (v, t))
  let exists v t = make_ (Exists (v, t))

  let ty_type = type_
  let ty_prop = prop

  let ty_builtin b = make_ (TyBuiltin b)
  let ty_const id = const id
  let ty_var v = var v
  let ty_app f l =
    if l=[] then f else app f l
  let ty_arrow a b = make_ (TyArrow (a,b))
  let ty_forall a b = make_ (TyForall(a,b))

  module Ty = struct
    type term = t
    type t = ty

    let view t = match t.view with
      | TyKind -> TyI.Kind
      | TyType -> TyI.Type
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | Var v -> TyI.Var v
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | TyForall (v,t) -> TyI.Forall (v,t)
      | Builtin _
      | Fun _
      | Forall _
      | Exists _
      | Let _ -> assert false

    let is_Type t = match t.view with
      | TyType -> true
      | _ -> false

    let is_Kind t = match t.view with
      | TyKind -> true
      | _ -> false

    let rec returns_Type t = match t.view with
      | TyType -> true
      | TyArrow (_, t')
      | TyForall (_, t') -> returns_Type t'
      | _ -> false

    let is_ty _ = true (* FIXME? remove from signature? *)

    let to_term t = t
    let of_term t = Some t
    let of_term_exn t = t

    module Subst = struct
      module M = Map.Make(struct
        type t = ty Var.t
        let compare = Var.compare
      end)

      type _t = ty M.t

      let empty = M.empty

      let is_empty = M.is_empty

      let find = M.find

      let bind = M.add

      let rec equal ~subst ty1 ty2 = match view ty1, view ty2 with
        | TyI.Kind, TyI.Kind
        | TyI.Type, TyI.Type -> true
        | TyI.Const id1, TyI.Const id2 -> ID.equal id1 id2
        | TyI.Var v1, _ when M.mem v1 subst ->
            equal ~subst (M.find v1 subst) ty2
        | _, TyI.Var v2 when M.mem v2 subst ->
            equal ~subst ty1 (M.find v2 subst)
        | TyI.Var v1, TyI.Var v2 -> Var.equal v1 v2
        | TyI.Builtin b1, TyI.Builtin b2 -> TyI.Builtin.equal b1 b2
        | TyI.Meta v1, TyI.Meta v2 -> NunMetaVar.equal v1 v2
        | TyI.App (f1,l1), TyI.App (f2, l2) ->
            equal ~subst f1 f2
              && List.length l1 = List.length l2
              && List.for_all2 (equal ~subst) l1 l2
        | TyI.Arrow (a1,b1), TyI.Arrow (a2,b2) ->
            equal ~subst a1 a2 && equal ~subst b1 b2
        | TyI.Forall (v1, t1), TyI.Forall (v2, t2) ->
            let v = Var.fresh_copy v1 in
            let subst = bind v1 (ty_var v) (bind v2 (ty_var v) subst) in
            equal ~subst t1 t2
        | TyI.Kind ,_
        | TyI.Var _, _
        | TyI.Type ,_
        | TyI.Builtin _,_
        | TyI.Const _,_
        | TyI.Meta _,_
        | TyI.App (_,_),_
        | TyI.Arrow (_,_),_
        | TyI.Forall (_,_),_ -> false

      let rec eval ~subst ty = match view ty with
        | TyI.Kind
        | TyI.Type
        | TyI.Meta _
        | TyI.Const _
        | TyI.Builtin _ -> ty
        | TyI.Var v ->
            begin try M.find v subst
            with Not_found -> ty
            end
        | TyI.App (f,l) ->
            ty_app (eval ~subst f) (List.map (eval ~subst) l)
        | TyI.Arrow (a,b) ->
            ty_arrow (eval ~subst a) (eval ~subst b)
        | TyI.Forall (v,t) ->
            let v' = Var.fresh_copy v in
            let subst = M.add v (ty_var v') subst in
            ty_forall v' (eval ~subst t)
    end

    include TyI.Print(struct type t = ty let view = view end)

    exception Error of string * t * t list
    (** Raised when a type application fails *)

    let () = Printexc.register_printer
      (function
        | Error (msg, t, l) ->
            let msg = CCFormat.sprintf
              "@[<hv2>type error@ when applying %a@ on @[%a@]: %s@]"
                print_in_app t (CCFormat.list print_in_app) l msg
            in Some msg
        | _ -> None
      )

    let error_ msg ~hd ~l = raise (Error (msg, hd, l))

    let apply t l =
      let rec app_ ~subst t l = match view t, l with
        | _, [] ->
            if Subst.is_empty subst then t else Subst.eval ~subst t
        | TyI.Kind, _
        | TyI.Type, _
        | TyI.Builtin _, _
        | TyI.App (_,_),_
        | TyI.Const _, _ ->
            error_ "cannot apply this type" ~hd:t ~l
        | TyI.Var v, _ ->
            begin try
              let t = Subst.find v subst in
              app_ ~subst t l
            with Not_found ->
              error_ "cannot apply this type" ~hd:t ~l
            end
        | TyI.Meta _,_ -> assert false
        | TyI.Arrow (a, t'), b :: l' ->
            if Subst.equal ~subst a b
            then app_ ~subst t' l'
            else error_ "type mismatch on first argument" ~hd:t ~l
        | TyI.Forall (v,t'), b :: l' ->
            let subst = Subst.bind v b subst in
            app_ ~subst t' l'

      in
      app_ ~subst:Subst.empty t l

    include TyI.Print(struct
      type _t = t
      type t = _t
      let view = view
    end)
  end

  type signature = t NunID.Map.t

  exception Undefined of id

  let () = Printexc.register_printer
    (function
      | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
      | _ -> None
    )

  let ty_of_eq =
    let v = Var.make ~ty:ty_type ~name:"a" in
    ty_forall v (ty_arrow (ty_var v) (ty_arrow (ty_var v) prop))

  let rec ty_exn ~sigma t = match t.view with
    | TyKind -> failwith "Term_ho.ty: kind has no type"
    | TyType -> kind_
    | Const id ->
        begin try NunID.Map.find id sigma
        with Not_found -> raise (Undefined id)
        end
    | Builtin b ->
        let module B = NunTerm_typed.Builtin in
        let prop1 = ty_arrow prop prop in
        let prop2 = ty_arrow prop (ty_arrow prop prop) in
        begin match b with
          | B.Eq -> ty_of_eq
          | B.Imply -> prop2
          | B.Equiv -> prop2
          | B.Or -> prop2
          | B.And -> prop2
          | B.Not -> prop1
          | B.True -> prop
          | B.False -> prop
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        Ty.apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Fun (v,t) ->
        if Ty.returns_Type (Var.ty v)
        then ty_forall v (ty_exn ~sigma t)
        else ty_arrow (Var.ty v) (ty_exn ~sigma t)
    | Forall (v,_)
    | Exists (v,_) -> ty_arrow (Var.ty v) prop
    | Let (_,_,u) -> ty_exn ~sigma u
    | TyBuiltin _
    | TyArrow (_,_)
    | TyForall (_,_) -> ty_type

  let ty ~sigma t =
    try CCError.return (ty_exn ~sigma t)
    with e -> NunUtils.err_of_exn e
end

