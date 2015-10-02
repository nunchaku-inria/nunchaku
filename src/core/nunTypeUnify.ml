
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

module Var = NunVar
module Sym = NunSymbol
module TyI = NunType_intf
module Utils = NunUtils

let section = Utils.Section.make "unif"

(*$inject
  module Var = NunVar
  module T = NunTerm_typed
  module Ty = T.Ty
  module U = Make(Ty)

*)

type var = Var.t
type 'a sequence = ('a -> unit) -> unit

module Make(Ty : NunType_intf.PRINTABLE) = struct
  exception Fail of (Ty.t * Ty.t) list * string

  let fpf = Format.fprintf
  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | Fail (stack, msg) ->
          let pp2 out (ty1,ty2) =
            fpf out "@[<hv2>trying to unify@ %a@ and %a@]" Ty.print ty1 Ty.print ty2
          in
          Some (spf "@[<hv2>unification error: %s:@ %a" msg (CCFormat.list pp2) stack)
      | _ -> None
    )

  (* does [var] occur in [ty]? *)
  let rec occur_check_ ~var ty =
    match Ty.view ty with
    | TyI.App (f, l) ->
        occur_check_ ~var f || List.exists (occur_check_ ~var) l
    | TyI.Kind
    | TyI.Type
    | TyI.Builtin _ -> false
    | TyI.Meta (v, ref) ->
        assert (NunDeref.can_bind ref);
        Var.equal v var
    | TyI.Var v -> Var.equal var v
    | TyI.Arrow (a,b) -> occur_check_ ~var a || occur_check_ ~var b
    | TyI.Forall (v,t) ->
        (* [var] could be shadowed *)
        not (Var.equal var v) && occur_check_ ~var t

  (* NOTE: after dependent types are added, will need to recurse into
      types too for unification and occur-check *)

  let push_ a b c = (a,b) :: c

  let fail ~stack msg = raise (Fail (stack, msg))

  let failf ~stack fmt =
    let b = Buffer.create 32 in
    let out = Format.formatter_of_buffer b in
    Format.kfprintf
      (fun _ -> Format.pp_print_flush out ();
        raise (Fail (stack, Buffer.contents b)))
      out fmt

  let rec flatten_app_ f l = match Ty.view f with
    | TyI.App (f1, l1) -> flatten_app_ f1 (l1 @ l)
    | _ -> f, l

  (* bound: set of bound variables, that cannot be unified *)
  let unify_exn ty1 ty2 =
    Utils.debugf ~section 5 "@[<2>unify %a@ and %a@]" Ty.print ty1 Ty.print ty2;
    let bound = ref Var.Map.empty in
    (* keep a stack of unification attempts *)
    let rec unify_ ~stack ty1 ty2 =
      let stack = push_ ty1 ty2 stack in
      match Ty.view ty1, Ty.view ty2 with
      | TyI.Kind, TyI.Kind
      | TyI.Type, TyI.Type -> ()  (* success *)
      | TyI.Builtin s1, TyI.Builtin s2 ->
          if TyI.Builtin.equal s1 s2 then ()
          else fail ~stack "incompatible symbols"
      | TyI.Var v1, TyI.Var v2 when Var.Map.mem v1 !bound ->
          if Var.equal v2 (Var.Map.find v1 !bound) then ()
          else failf ~stack "variable %a is bound" Var.print v1
      | TyI.Var v1, TyI.Var v2 when Var.Map.mem v2 !bound ->
          if Var.equal v1 (Var.Map.find v2 !bound) then ()
          else failf ~stack "variable %a is bound" Var.print v2
      | TyI.Meta (v1, _), TyI.Meta (v2, _)
      | TyI.Var v1, TyI.Var v2 when Var.equal v1 v2 -> ()
      | TyI.Meta (var, ref), _ when NunDeref.can_bind ref ->
          if occur_check_ ~var:var ty2
            then
              failf ~stack
                "cycle detected (variable %a occurs in type)" Var.print var
            else NunDeref.bind ~ref ty2
      | _, TyI.Meta (var, ref) when NunDeref.can_bind ref ->
          if occur_check_ ~var:var ty1
            then
              failf ~stack
                "cycle detected (variable %a occurs in type)" Var.print var
            else NunDeref.bind ~ref ty1
      | TyI.App (f1,l1), TyI.App (f2,l2) ->
          (* NOTE: if partial application in types is allowed,
             we must allow [length l1 <> length l2]. In that case, unification
             proceeds from the right *)
          let f1, l1 = flatten_app_ f1 l1 in
          let f2, l2 = flatten_app_ f2 l2 in
          if List.length l1<>List.length l2
            then
              failf ~stack
                "different number of arguments (%d and %d resp.)"
                (List.length l1) (List.length l2);
          unify_ ~stack f1 f2;
          List.iter2 (unify_ ~stack) l1 l2
      | TyI.Arrow (l1,r1), TyI.Arrow (l2,r2) ->
          unify_ ~stack l1 l2;
          unify_ ~stack r1 r2
      | TyI.Forall (v1,t1), TyI.Forall (v2,t2) ->
          assert (not (Var.Map.mem v1 !bound));
          assert (not (Var.Map.mem v2 !bound));
          bound := Var.Map.add v1 v2 !bound;
          unify_ ~stack t1 t2
      | TyI.Meta _, _
      | TyI.Var _, _
      | TyI.Kind, _
      | TyI.Type, _
      | TyI.Builtin _,_
      | TyI.App (_,_),_
      | TyI.Arrow (_,_),_
      | TyI.Forall (_,_),_ ->
          fail ~stack "incompatible types"
    in
    unify_ ~stack:[] ty1 ty2

  (*$R
    let v = T.ty_meta_var (Var.make ~name:"x") in
    let f = T.ty_var (Var.make ~name:"f") in
    let a' = Var.make ~name:"a" in
    let a = T.ty_var a' in
    let t1 = T.ty_app f [v] in
    let t2 = T.ty_app f [a] in
    U.unify_exn t1 t2;
    assert_bool "v is a"
      (match Ty.view v with
        | NunType_intf.Var v' -> Var.equal v' a'
        | _ -> false
      );
  *)

  let rec eval ty = match Ty.view ty with
    | TyI.Kind
    | TyI.Type
    | TyI.Meta _
    | TyI.Var _
    | TyI.Builtin _ -> ty
    | TyI.App (f,l) -> Ty.build (TyI.App (eval f, List.map eval l))
    | TyI.Arrow (a,b) -> Ty.build (TyI.Arrow (eval a, eval b))
    | TyI.Forall (v,t) -> Ty.build (TyI.Forall (v, eval t))

  type meta_vars_set = Ty.t NunDeref.t NunVar.Map.t
  (* a set of meta-variable with their reference *)

  let free_meta_vars ?(init=Var.Map.empty) ty =
    let rec aux acc ty =
      match Ty.view ty with
      | TyI.Kind | TyI.Type | TyI.Builtin _ -> acc
      | TyI.Meta (v, ref) ->
          assert (NunDeref.can_bind ref);
          Var.Map.add v ref acc
      | TyI.Var _ -> acc
      | TyI.App (f,l) ->
          let acc = aux acc f in
          List.fold_left aux acc l
      | TyI.Arrow (a,b) ->
          let acc = aux acc a in
          aux acc b
      | TyI.Forall (_,t) ->
          (* the variable should not be a meta *)
          aux acc t
    in
    aux init ty
end


