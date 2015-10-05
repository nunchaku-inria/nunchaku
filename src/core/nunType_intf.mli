
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Types} *)

type id = NunID.t
type 'a var = 'a NunVar.t

type ('a, 'kind) view =
  | Kind : ('a, [>]) view (** the "type" of [Type], in some sense *)
  | Type : ('a, [>]) view (** the type of types *)
  | Builtin : NunBuiltin.Ty.t -> ('a, [>]) view (** Builtin type *)
  | Const : id -> ('a, [>]) view
  | Var : 'a var -> ('a, [>]) view (** Constant or bound variable *)
  | Meta : 'a NunMetaVar.t -> ('a, [>`Meta]) view (** Meta-variable, used for unification *)
  | App : 'a * 'a list -> ('a, [>]) view
  | Arrow : 'a * 'a -> ('a, [>]) view
  | Forall : 'a var * 'a -> ('a, [>`Poly]) view  (** Polymorphic type *)

(** {2 Basic Interface} *)
module type S = sig
  type t

  val view : t -> (t, 'kind) view
  (** View must follow {!deref} pointers *)
end

module type AS_TERM = sig
  type term
  type t = private term

  include S with type t := t

  val is_Type : t -> bool (** type == Type? *)
  val returns_Type : t -> bool (** type == forall ... -> ... -> ... -> Type? *)
  val is_Kind : t -> bool (** type == Kind? *)

  val to_term : t -> term
  val is_ty : term -> bool (** [is_ty t] same as [is_Type (type of t)] *)
  val of_term : term -> t option
  val of_term_exn : term -> t  (** @raise Failure if it is not a term *)
end

module type PRINTABLE = sig
  include S
  include NunIntf.PRINT with type t := t
end

(** {2 Print Types} *)

type 'a printer = Format.formatter -> 'a -> unit

module Print(Ty : S) : sig
  val print : Ty.t printer
  val print_in_app : Ty.t printer
  val print_in_arrow : Ty.t printer
end
