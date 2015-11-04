
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

module ID = NunID
module Var = NunVar
module MetaVar = NunMetaVar
module M = NunMark

type id = NunID.t
type 'a var = 'a Var.t
type 'a printer = Format.formatter -> 'a -> unit

type ('a, 'inv) view =
  | Builtin of NunBuiltin.Ty.t (** Builtin type *)
  | Const of id
  | Var :
      'a var (** Constant or bound variable *)
      -> ('a, <poly:NunMark.polymorph;..>) view
  | Meta :
      'a NunMetaVar.t (** Meta-variable, used for unification *)
      -> ('a, <meta: NunMark.with_meta;..>) view
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall :   (** Polymorphic type *)
      'a var
      * 'a
      -> ('a, <poly: NunMark.polymorph;..>) view

(** {2 Basic Interface} *)
module type S = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  type t

  val view : t -> (t, invariant) view
  (** View must follow {!deref} pointers *)
end

module type UTILS = sig
  type t
  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val returns : t -> t (** follow forall/arrows to get return type.  *)
  val is_Kind : t -> bool (** type == Kind? *)
  val to_seq : t -> t Sequence.t
end

module type AS_TERM = sig
  type term
  type t = term

  include S with type t := t
  include UTILS with type t := t
end

module type PRINTABLE = sig
  include S
  include NunIntf.PRINT with type t := t
end

(** {2 Utils} *)
module Utils(Ty : S) : UTILS with type t = Ty.t = struct
  type t = Ty.t

  let is_Type t = match Ty.view t with
    | Builtin NunBuiltin.Ty.Type -> true
    | _ -> false

  let is_Kind t = match Ty.view t with
    | Builtin NunBuiltin.Ty.Kind -> true
    | _ -> false

  let rec returns t = match Ty.view t with
    | Arrow (_, t') -> returns t'
    | Forall (_, t') -> returns t'
    | _ -> t

  let returns_Type t = match Ty.view (returns t) with
    | Builtin NunBuiltin.Ty.Type -> true
    | _ -> false

  let to_seq ty yield =
    let rec aux (ty:t) =
      yield ty;
      match Ty.view ty with
      | Builtin _
      | Const _ -> ()
      | Var _ -> ()
      | Meta _ -> ()
      | App (f,l) -> aux f; List.iter aux l
      | Arrow (a,b) -> aux a; aux b
      | Forall (_,t) -> aux t
    in aux ty
end

(** {2 Print Types} *)

module Print(Ty : S) = struct
  let fpf = Format.fprintf

  let rec print out ty = match Ty.view ty with
    | Builtin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Meta v -> MetaVar.print out v
    | Const id -> ID.print_no_id out id
    | Var v -> Var.print out v
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Arrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_arrow a print b
    | Forall (v,t) ->
        fpf out "@[<2>pi %a:type.@ %a@]" Var.print v print t
  and print_in_app out t = match Ty.view t with
    | Builtin _ | Const _ -> print out t
    | Var _ -> print out t
    | Meta _ -> print out t
    | App (_,_)
    | Arrow (_,_) -> fpf out "@[(%a)@]" print t
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match Ty.view t with
    | Builtin _ | Const _ | App (_,_) -> print out t
    | Var _ -> print out t
    | Meta _ -> print out t
    | Arrow (_,_) -> fpf out "@[(%a)@]" print t
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
end
