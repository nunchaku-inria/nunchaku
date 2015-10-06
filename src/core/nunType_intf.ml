
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

module ID = NunID
module Var = NunVar
module MetaVar = NunMetaVar

type id = NunID.t
type 'a var = 'a Var.t

type 'a view =
  | Kind (** the "type" of [Type], in some sense *)
  | Type (** the type of types *)
  | Builtin of NunBuiltin.Ty.t (** Builtin type *)
  | Const of id
  | Var of 'a var (** Constant or bound variable *)
  | Meta of 'a NunMetaVar.t (** Meta-variable, used for unification *)
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of 'a var * 'a  (** Polymorphic type *)

(** {2 Basic Interface} *)
module type S = sig
  type t

  val view : t -> t view
end

module type AS_TERM = sig
  type term
  type t = private term

  include S with type t := t

  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val is_Kind : t -> bool (** type == Kind? *)
  val to_term : t -> term

  val of_term_unsafe : term -> t
  (** [of_term_unsafe t] converts [t] to a [ty] without checking.
      {b caution}, this can break invariants. *)
end

module type PRINTABLE = sig
  include S
  include NunIntf.PRINT with type t := t
end

(** {2 Print Types} *)

type 'a printer = Format.formatter -> 'a -> unit

module Print(Ty : S) = struct
  let fpf = Format.fprintf

  let rec print out ty = match Ty.view ty with
    | Kind -> CCFormat.string out "kind"
    | Type -> CCFormat.string out "type"
    | Builtin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Meta v -> ID.print out (MetaVar.id v)
    | Const id -> ID.print out id
    | Var v -> Var.print out v
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Arrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_arrow a print b
    | Forall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print t
  and print_in_app out t = match Ty.view t with
    | Builtin _ | Kind | Type | Var _ | Const _ | Meta _ -> print out t
    | App (_,_)
    | Arrow (_,_)
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match Ty.view t with
    | Builtin _ | Kind | Type | Var _ | Const _ | Meta _
    | App (_,_) -> print out t
    | Arrow (_,_)
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
end
