
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main Term Interface} *)

module Var = NunVar
module TyI = NunType_intf

type var = Var.t

module Builtin : sig
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
  val fixity : t -> [`Infix | `Prefix]
  val to_string : t -> string
  val equal : t -> t -> bool
end = struct
  type t =
    | True
    | False
    | Not
    | Or
    | And
    | Imply
    | Equiv
  let fixity = function
    | True
    | False
    | Not -> `Prefix
    | Or
    | And
    | Imply
    | Equiv -> `Infix
  let to_string = function
    | True -> "true"
    | False -> "false"
    | Not -> "~"
    | Or -> "|"
    | And -> "&"
    | Imply -> "=>"
    | Equiv -> "<=>"
  let equal = (==)
end

type ('a, 'ty) view =
  | Builtin of Builtin.t (** built-in symbol *)
  | Var of var (** variable, bound or free *)
  | App of 'a * 'a list
  | Fun of var * 'ty * 'a
  | Forall of var * 'ty * 'a
  | Exists of var * 'ty * 'a
  | Let of var * 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunType_intf.Builtin.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of var * 'ty  (** Polymorphic/dependent type *)

(** {2 What is a term?} *)
module type S = sig
  type t
  (** Represents both terms and types *)

  module Ty : NunType_intf.AS_TERM with type term = t

  val view : t -> (t, Ty.t) view

  val build : (t, Ty.t) view -> t
end

module type S_WITH_UNIFIABLE_TY = sig
  type t

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t
    include NunType_intf.UNIFIABLE with type t := t
  end

  val view : t -> (t, Ty.t) view

  val build : (t, Ty.t) view -> t
end

(** {2 Print Terms} *)

module Print(T : S) : sig
  type 'a printer = Format.formatter -> 'a -> unit

  val print : T.t printer
  val print_in_app : T.t printer
  val print_in_binder : T.t printer
end = struct
  type 'a printer = Format.formatter -> 'a -> unit

  let fpf = Format.fprintf

  let rec print out ty = match T.view ty with
    | TyKind -> CCFormat.string out "kind"
    | TyType -> CCFormat.string out "type"
    | Builtin b -> CCFormat.string out (Builtin.to_string b)
    | TyBuiltin b -> CCFormat.string out (TyI.Builtin.to_string b)
    | Var v -> Var.print out v
    | App (f, [a;b]) ->
        begin match T.view f with
        | Builtin s when Builtin.fixity s = `Infix ->
            fpf out "@[<2>%a@ %s@ %a@]"
              print_in_app a (Builtin.to_string s) print_in_app b
        | _ ->
            fpf out "@[<2>%a@ %a@ %a@]" print_in_app f
              print_in_app a print_in_app b
        end
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print v print t print u
    | Fun (v, ty, t) ->
        fpf out "@[<2>fun %a:%a.@ %a@]" Var.print v print_ty_in_app ty print t
    | Forall (v, ty, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app ty print t
    | Exists (v, ty, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app ty print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_ty_in_app a print_ty_in_arrow b
    | TyForall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print_ty t

  and print_ty out ty = print out (T.Ty.to_term ty)
  and print_ty_in_app out ty = print_in_app out (T.Ty.to_term ty)
  and print_ty_in_arrow out ty = print_in_binder out (T.Ty.to_term ty)

  and print_in_app out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType | Var _ -> print out t
    | App (_,_)
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t

  and print_in_binder out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType | Var _ | App (_,_) ->
        print out t
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t
end
