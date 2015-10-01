
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module Ty = NunType_intf
module Loc = NunLocation

type loc = NunLocation.t
type sym = NunSymbol.t

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

