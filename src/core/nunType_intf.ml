
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

type ('t, 'inv) repr = ('t -> ('t, 'inv) view)
(** A representation of types with concrete type ['t], and invariants
    ['inv].
    The view function must follow {!deref} pointers *)

let view ~repr t = repr t

let is_Type ~repr t = match repr t with
  | Builtin NunBuiltin.Ty.Type -> true
  | _ -> false

let is_Kind ~repr t = match repr t with
  | Builtin NunBuiltin.Ty.Kind -> true
  | _ -> false

let rec returns
: type t inv. repr:(t,inv) repr -> t -> t
= fun ~repr t -> match repr t with
  | Arrow (_, t') -> returns ~repr t'
  | Forall (_, t') -> returns ~repr t'
  | _ -> t

let returns_Type ~repr t = match repr (returns ~repr t) with
  | Builtin NunBuiltin.Ty.Type -> true
  | _ -> false

let to_seq
: type inv t. repr:(t, inv) repr -> t -> t Sequence.t
= fun ~repr ty yield ->
  let rec aux : t -> unit = fun ty ->
    yield ty;
    match repr ty with
    | Builtin _
    | Const _ -> ()
    | Var _ -> ()
    | Meta _ -> ()
    | App (f,l) -> aux f; List.iter aux l
    | Arrow (a,b) -> aux a; aux b
    | Forall (_,t) -> aux t
  in aux ty

type packed = Packed : 't * ('t, _) repr -> packed

let pack ~repr t = Packed (t,repr)

(** {2 Print Types} *)

type 't print_funs = {
  print: 't printer;
  print_in_app: 't printer;
  print_in_arrow: 't printer;
}

let fpf = Format.fprintf

let mk_print
: type t inv. repr:(t,inv)repr -> t print_funs
= fun ~repr ->
  let rec print out (ty:t) = match repr ty with
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
  and print_in_app out t = match repr t with
    | Builtin _ | Const _ -> print out t
    | Var _ -> print out t
    | Meta _ -> print out t
    | App (_,_)
    | Arrow (_,_) -> fpf out "@[(%a)@]" print t
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
  and print_in_arrow out t = match repr t with
    | Builtin _ | Const _ | App (_,_) -> print out t
    | Var _ -> print out t
    | Meta _ -> print out t
    | Arrow (_,_) -> fpf out "@[(%a)@]" print t
    | Forall (_,_) -> fpf out "@[(%a)@]" print t
  in
  { print; print_in_app; print_in_arrow; }

let print ~repr = (mk_print ~repr).print
let print_in_app ~repr = (mk_print ~repr).print_in_app
let print_in_arrow ~repr = (mk_print ~repr).print_in_arrow
