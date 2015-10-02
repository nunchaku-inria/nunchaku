
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

module Var = NunVar

type var = Var.t

module Builtin : sig
  type t =
    | Prop
  val equal : t -> t -> bool
  val to_string : t -> string
end = struct
  type t =
    | Prop
  let equal = (==)
  let to_string = function
    | Prop -> "prop"
end

type 'a view =
  | Kind (** the "type" of [Type], in some sense *)
  | Type (** the type of types *)
  | Builtin of Builtin.t (** Builtin type *)
  | Var of var
  | App of 'a * 'a list
  | Arrow of 'a * 'a
  | Forall of var * 'a  (** Polymorphic type *)

(** {2 Basic Interface: view, build} *)
module type S = sig
  type t

  val view : t -> t view

  val build : t view -> t

  val fold : ('a view -> 'a) -> t -> 'a
end

module type AS_TERM = sig
  type term
  type t = private term

  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val is_Kind : t -> bool (** type == Kind? *)

  val to_term : t -> term
  val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  val of_term : term -> t option
  val of_term_exn : term -> t  (** @raise Failure if it is not a term *)
end

(** {2 Types with bindings, for unification} *)
module type UNIFIABLE = sig
  include S

  val deref : t -> t option

  val can_bind : t -> bool
  (** [can_bind t] returns [true]  iff [t] is a type {b meta}-variable that is
      not bound *)

  val bind : var:t -> t -> unit
  (** [bind ~var t] binds the variable [var] to [t].
      @raise Invalid_argument if [var] is not a variable or if [var]
        is already bound *)

  include NunIntf.PRINT with type t := t
  (** Need to be able to print types *)
end

(** {2 Print Types} *)

module Print(Ty : S) : sig
  type 'a printer = Format.formatter -> 'a -> unit

  val print : Ty.t printer
  val print_in_app : Ty.t printer
  val print_in_arrow : Ty.t printer
end = struct
  type 'a printer = Format.formatter -> 'a -> unit

  let fpf = Format.fprintf

  let rec print out ty = match Ty.view ty with
    | Kind -> CCFormat.string out "kind"
    | Type -> CCFormat.string out "type"
    | Builtin b -> CCFormat.string out (Builtin.to_string b)
    | Var v -> Var.print out v
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Arrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_app a print_in_arrow b
    | Forall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print t
  and print_in_app out t = match Ty.view t with
    | Builtin _ | Kind | Type | Var _ -> print out t
    | App (_,_)
    | Arrow (_,_)
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match Ty.view t with
    | Builtin _ | Kind | Type | Var _
    | App (_,_) -> print out t
    | Arrow (_,_)
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
end
