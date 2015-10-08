
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

module MetaVar = NunMetaVar
module ID = NunID
module Var = NunVar
module TyI = NunType_intf
module Utils = NunUtils

let section = Utils.Section.make "unif"

(*$inject
  module Var = NunVar
  module MetaVar = NunMetaVar
  module T = NunTerm_typed.Default
  module ID = NunID
  module Ty = T.Ty
  module U = Make(Ty)

*)

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
    | TyI.Var _ (* bound var *)
    | TyI.Const _
    | TyI.Builtin _ -> false
    | TyI.Meta var' ->
        assert (MetaVar.can_bind var');
        MetaVar.equal var var'
    | TyI.Arrow (a,b) -> occur_check_ ~var a || occur_check_ ~var b
    | TyI.Forall (_,t) -> occur_check_ ~var t

  (* NOTE: after dependent types are added, will need to recurse into
      types too for unification and occur-check *)

  let push_ a b c = (a,b) :: c

  let fail ~stack msg = raise (Fail (stack, msg))

  let failf ~stack fmt =
    NunUtils.exn_ksprintf fmt
      ~f:(fun msg -> raise (Fail (stack, msg)))

  let rec flatten_app_ f l = match Ty.view f with
    | TyI.App (f1, l1) -> flatten_app_ f1 (l1 @ l)
    | _ -> f, l

  module VarMap = Map.Make(struct
    type t = Ty.t Var.t
    let compare = Var.compare
  end)

  (* bound: set of bound variables, that cannot be unified *)
  let unify_exn ty1 ty2 =
    Utils.debugf ~section 5 "@[<2>unify %a@ and %a@]" Ty.print ty1 Ty.print ty2;
    let bound = ref VarMap.empty in
    (* keep a stack of unification attempts *)
    let rec unify_ ~stack ty1 ty2 =
      let stack = push_ ty1 ty2 stack in
      match Ty.view ty1, Ty.view ty2 with
      | TyI.Kind, TyI.Kind
      | TyI.Type, TyI.Type -> ()  (* success *)
      | TyI.Builtin s1, TyI.Builtin s2 ->
          if NunBuiltin.Ty.equal s1 s2 then ()
          else fail ~stack "incompatible symbols"
      | TyI.Const i1, TyI.Const i2 ->
          if ID.equal i1 i2 then () else fail ~stack "incompatible symbols"
      | TyI.Var v1, TyI.Var v2 when Var.equal v1 v2 -> ()
      | TyI.Var v1, TyI.Var v2 ->
          begin try
            let var = VarMap.find v1 !bound in
            let var' = VarMap.find v2 !bound in
            if Var.equal var var' then ()
            else failf ~stack "bound variables %a and %a are incompatible"
              Var.print v1 Var.print v2
          with Not_found ->
            fail ~stack "incompatible variables"
          end
      | TyI.Meta v1, TyI.Meta v2 when MetaVar.equal v1 v2 -> ()
      | TyI.Meta var, _ when MetaVar.can_bind var ->
          if occur_check_ ~var ty2
            then
              failf ~stack
                "cycle detected (variable %a occurs in type)" MetaVar.print var
            else MetaVar.bind ~var ty2
      | _, TyI.Meta var when MetaVar.can_bind var ->
          if occur_check_ ~var ty1
            then
              failf ~stack
                "cycle detected (variable %a occurs in type)" MetaVar.print var
            else MetaVar.bind ~var ty1
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
          assert (not (VarMap.mem v1 !bound));
          assert (not (VarMap.mem v2 !bound));
          let v = Var.make ~ty:(Var.ty v1) ~name:"?" in
          bound := VarMap.add v1 v (VarMap.add v2 v !bound);
          unify_ ~stack t1 t2
      | TyI.Meta _, _
      | TyI.Const _, _
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
    let v = T.ty_meta_var (MetaVar.make ~name:"x") in
    let f = T.ty_var (Var.make ~ty:T.ty_type ~name:"f") in
    let a' = ID.make ~name:"a" in
    let a = T.ty_const a' in
    let t1 = T.ty_app f [v] in
    let t2 = T.ty_app f [a] in
    U.unify_exn t1 t2;
    assert_bool "v is a"
      (match Ty.view v with
        | NunType_intf.Const id' -> ID.equal a' id'
        | _ -> false
      );
  *)

  type meta_vars_set = Ty.t MetaVar.t ID.Map.t
  (* a set of meta-variable with their reference *)

  let free_meta_vars ?(init=ID.Map.empty) ty =
    let rec aux acc ty =
      match Ty.view ty with
      | TyI.Kind | TyI.Type | TyI.Builtin _ | TyI.Const _ | TyI.Var _ -> acc
      | TyI.Meta var ->
          assert (MetaVar.can_bind var);
          ID.Map.add (MetaVar.id var) var acc
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


