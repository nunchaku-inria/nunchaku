
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module T = NunTerm_intf
module Sym = NunSymbol
module Loc = NunLocation

(** {1 Terms with Types} *)

module Make(Ty : NunTypeInference.TYPE) :
  NunTypeInference.TERM with module Ty = Ty
= struct

  module Ty = Ty

  type ty = Ty.t

  type t = {
    view : (t, Ty.t) T.view;
    loc : Loc.t option;
    mutable ty : Ty.t option;
  }

  let view t = t.view

  let loc t = t.loc

  let ty t = t.ty

  let make_raw_ ~loc ~ty view = { view; loc; ty }

  let make_ ?loc ?ty view = match view with
    | T.App ({view=T.App (f, tys, l1); loc; _}, [], l2) ->
        make_raw_ ~loc ~ty (T.App (f, tys, l1 @ l2))
    | _ -> make_raw_ ~loc ~ty view

  let build t = make_ t

  let prop_ = Ty.sym Sym.prop

  let sym ?loc ~ty s = make_ ?loc ~ty (T.Sym s)
  let var ?loc ~ty v = make_ ?loc ~ty (T.Var v)
  let app ?loc ~ty t ~ty_arg l = make_ ?loc ~ty (T.App (t, ty_arg, l))
  let fun_ ?loc ~ty v ~ty_arg t = make_ ?loc ~ty (T.Fun (v, ty_arg, t))
  let let_ ?loc v t u = make_ ?loc ?ty:u.ty (T.Let (v, t, u))
  let forall ?loc v ~ty_arg t = make_ ?loc ~ty:prop_ (T.Forall (v, ty_arg, t))
  let exists ?loc v ~ty_arg t = make_ ?loc ~ty:prop_ (T.Exists (v, ty_arg, t))

end
