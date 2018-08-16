
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphic Types} *)

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

  type nonrec 'a view = 'a view =
    | Builtin of Builtin.t (** Builtin type *)
    | Const of id
    | App of 'a * 'a list
    | Arrow of 'a * 'a

  val is_ty : T.t -> bool

  val repr : T.t -> T.t view
  (** [repr t] returns the view of [t] as a type.
      precondition: [is_ty t]
      raise some exception otherwise *)

  val as_ty : T.t -> T.t view option
  (** [as_ty t] returns [Some view] if [is_ty t, repr t = view], and
      returns [None] otherwise *)

  val repr_with : subst:(T.t,T.t) Subst.t -> T.t -> T.t view
  (** representation that follows the substitution. Will
      fail on a variable, except if it is bound *)

  val mangle : sep:string -> T.t -> string
  (** serialize the whole type into a flat name *)

  module Map : CCMap.S with type key = T.t
  (** A map on terms that only accepts terms
      satisfying [is_ty] as keys *)
end

module Make(T : TI.REPR)
  : S with module T = T
= struct
  module T = T

  type nonrec 'a view = 'a view =
    | Builtin of Builtin.t (** Builtin type *)
    | Const of id
    | App of 'a * 'a list
    | Arrow of 'a * 'a


  let rec is_ty t = match T.repr t with
    | TI.TyBuiltin _
    | TI.Const _ -> true
    | TI.App (f,l) -> is_ty f && List.for_all is_ty l
    | TI.TyArrow (a,b) -> is_ty a && is_ty b
    | TI.TyMeta _
    | TI.Var _
    | TI.Builtin _
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
    | TI.Builtin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> assert false

  let as_ty t = try Some (repr t) with Assert_failure _ -> None

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
    | TI.Builtin _
    | TI.Match _
    | TI.Let _
    | TI.Bind _ -> assert false

  (* mangle the type into a valid identifier *)
  let mangle ~sep t =
    let rec pp_ out t = match repr t with
      | Builtin b -> CCFormat.string out (Builtin.to_string b)
      | Arrow (a,b) -> Format.fprintf out "%a_to_%a" pp_ a pp_ b
      | Const id -> ID.pp_name out id
      | App (_,[]) -> assert false
      | App (a,l) ->
        Format.fprintf out "%a_%a"
          pp_ a (Utils.pp_list ~sep pp_) l
    in
    CCFormat.sprintf "@[<h>%a@]" pp_ t

  let to_int_ = function
    | Builtin _ -> 0
    | Const _ -> 1
    | App _ -> 2
    | Arrow _ -> 3

  let rec cmp_ty a b = match repr a, repr b with
    | Const id1, Const id2 -> ID.compare id1 id2
    | Builtin b1, Builtin b2 -> Builtin.compare b1 b2
    | App (c1,l1), App (c2,l2) ->
      CCOrd.( cmp_ty c1 c2 <?> (list cmp_ty, l1, l2))
    | Arrow (l1,r1), Arrow (l2,r2) -> CCOrd.( cmp_ty l1 l2 <?> (cmp_ty, r1, r2))
    | Const _, _ | App _, _ | Arrow _, _ | Builtin _, _ ->
      Pervasives.compare (to_int_ (repr a)) (to_int_ (repr b))

  module Map = CCMap.Make(struct
      type t = T.t
      let compare = cmp_ty
    end)
end

module Default = Make(Term)
