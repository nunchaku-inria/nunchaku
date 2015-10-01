
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module Ty = NunType_intf
module Loc = NunLocation
module Sym = NunSymbol
module Var = NunVar

type loc = Loc.t
type sym = Sym.t

(** {1 Types for Type Inference} *)

type t = {
  view: t Ty.view;
  loc: loc option;
  mutable deref: t option;  (* for variable binding *)
}

let view t = t.view

let make_raw_ ~loc view = { view; loc; deref=None }

let make_ ?loc view = match view with
  | Ty.App (f, []) -> f
  | Ty.App ({view=Ty.App (f,l1); _}, l2) ->
      make_raw_ ~loc (Ty.App (f, l1@l2))  (* flattening *)
  | _ -> make_raw_ ~loc view

let rec fold fun_ t = match t.view with
  | Ty.Var v -> fun_ (Ty.Var v)
  | Ty.Sym s -> fun_ (Ty.Sym s)
  | Ty.App (f,l) ->
      let f = fold fun_ f in
      let l = List.map (fold fun_) l in
      fun_ (Ty.App (f,l))
  | Ty.Arrow (a,b) -> fun_ (Ty.Arrow (fold fun_ a, fold fun_ b))
  | Ty.Forall (v,t) -> fun_ (Ty.Forall (v, fold fun_ t))

let sym ?loc s = make_ ?loc (Ty.Sym s)
let var ?loc v = make_ ?loc (Ty.Var v)
let app ?loc f l = make_ ?loc (Ty.App (f,l))
let arrow ?loc a b = make_ ?loc (Ty.Arrow (a,b))
let forall ?loc v t = make_ ?loc (Ty.Forall (v,t))

let build s = make_ s

let loc t = t.loc

(* dereference the type, if it is a variable, until it is not bound *)
let rec deref t = match t.deref with
  | None -> None
  | Some t' as res ->
      match deref t' with
      | None -> res  (* t' is root *)
      | Some _ as res ->
          (* path compression *)
          t.deref <- res;
          res

let is_var t = match t.view with Ty.Var _ -> true | _ -> false

let bind ~var t =
  if not (is_var var) then invalid_arg "Type_mut.bind";
  if var.deref <> None then invalid_arg "Type_mut.bind";
  var.deref <- Some t

let fpf = Format.fprintf

let rec print out ty = match ty.view with
  | Ty.Sym s -> Sym.print out s
  | Ty.Var v -> Var.print out v
  | Ty.App (f,l) ->
      fpf out "@[<2>%a@ %a@]" print_in_app f
        (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
  | Ty.Arrow (a,b) ->
      fpf out "@[<2>%a ->@ %a@]" print_in_app a print_in_arrow b
  | Ty.Forall (v,t) ->
      fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print t
and print_in_app out t = match t.view with
  | Ty.Sym _
  | Ty.Var _ -> print out t
  | Ty.App (_,_)
  | Ty.Arrow (_,_)
  | Ty.Forall (_,_) -> fpf out "@[(%a)@]" print t
and print_in_arrow out t = match t.view with
  | Ty.Sym _
  | Ty.Var _
  | Ty.App (_,_) -> print out t
  | Ty.Arrow (_,_)
  | Ty.Forall (_,_) -> fpf out "@[(%a)@]" print t
