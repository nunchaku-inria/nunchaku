
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

module MetaVar = NunMetaVar
module ID = NunID
module Var = NunVar
module TI = NunTermInner
module TyI = NunTypePoly
module Utils = NunUtils
module Subst = Var.Subst

let section = Utils.Section.make "unif"

(*$inject
  module Var = NunVar
  module MetaVar = NunMetaVar
  module TI = NunTermInner
  module T = NunTermTyped.Default
  module U = NunTermTyped.Util(T)
  module ID = NunID
  module Unif = Make(T)

  let repr = T.repr

*)

type 'a sequence = ('a -> unit) -> unit

module Make(T : TI.REPR) = struct
  module P = TI.Print(T)
  module Ty = NunTypePoly.Make(T)

  exception Fail of (T.t * T.t) list * string
  (** Raised when unification fails. The list of pairs of types is the
      unification stack (with the innermost types first) *)

  let fpf = Format.fprintf
  let spf = CCFormat.sprintf

  let pp_ty = P.print

  let () = Printexc.register_printer
    (function
      | Fail (stack, msg) ->
          let pp2 out (ty1,ty2) =
            fpf out "@[<hv2>trying to unify@ `%a`@ and `%a`@]"
              pp_ty ty1 pp_ty ty2
          in
          Some (spf "@[<hv2>unification error: %s:@ %a"
            msg (CCFormat.list pp2) stack)
      | _ -> None
    )

  (* does [var] occur in [ty]? *)
  let rec occur_check_ ~var ty =
    match Ty.repr ty with
    | TyI.App (f, l) ->
        occur_check_ ~var f || List.exists (occur_check_ ~var) l
    | TyI.Var _ -> false (* bound var *)
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

  let rec flatten_app_ f l = match Ty.repr f with
    | TyI.App (f1, l1) -> flatten_app_ f1 (l1 @ l)
    | _ -> f, l

  (* bound: set of bound variables, that cannot be unified *)
  let unify_exn ty1 ty2 =
    Utils.debugf ~section 5 "@[<hv2>unify `@[%a@]`@ and `@[%a@]`@]"
      (fun k-> k pp_ty ty1 pp_ty ty2);
    let bound = ref Subst.empty in
    (* keep a stack of unification attempts *)
    let rec unify_ ~stack ty1 ty2 =
      let stack = push_ ( ty1) ( ty2) stack in
      match Ty.repr ty1, Ty.repr ty2 with
      | TyI.Builtin s1, TyI.Builtin s2 ->
          if TI.TyBuiltin.equal s1 s2 then ()
          else fail ~stack "incompatible symbols"
      | TyI.Const i1, TyI.Const i2 ->
          if ID.equal i1 i2 then () else fail ~stack "incompatible symbols"
      | TyI.Var v1, TyI.Var v2 when Var.equal v1 v2 -> ()
      | TyI.Var v1, TyI.Var v2 ->
          begin try
            let var = Subst.find_exn ~subst:!bound v1 in
            let var' = Subst.find_exn ~subst:!bound v2 in
            if Var.equal var var' then ()
            else failf ~stack "bound variables %a and %a are incompatible"
              Var.print v1 Var.print v2
          with Not_found ->
            fail ~stack "incompatible variables"
          end
      | TyI.Meta v1, TyI.Meta v2 when MetaVar.equal v1 v2 -> ()
      | TyI.Meta var, _ when MetaVar.can_bind var ->
          (* TODO: check that ty2 is closed! not bound vars allowed *)
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
          assert (not (Subst.mem ~subst:!bound v1));
          assert (not (Subst.mem ~subst:!bound v2));
          let v = Var.make ~ty:(Var.ty v1) ~name:"?" in
          bound := Subst.add ~subst:(Subst.add ~subst:!bound v2 v) v1 v;
          unify_ ~stack t1 t2
      | TyI.Const _, _
      | TyI.Builtin _,_
      | TyI.App (_,_),_
      | TyI.Arrow (_,_),_ ->
          fail ~stack "incompatible types"
      | TyI.Var _, _ -> fail ~stack "incompatible types"
      | TyI.Forall (_,_),_ -> fail ~stack "incompatible types"
      | TyI.Meta _, _ -> fail ~stack "incompatible types"
    in
    unify_ ~stack:[] ty1 ty2

  (*$R
    let v = U.ty_meta_var (MetaVar.make ~name:"x") in
    let f = U.ty_var (Var.make ~ty:U.ty_type ~name:"f") in
    let a' = ID.make ~name:"a" in
    let a = U.ty_const a' in
    let t1 = U.ty_app f [v] in
    let t2 = U.ty_app f [a] in
    Unif.unify_exn t1 t2;
    assert_bool "v is a"
      (match T.repr v with
        | TI.Const id' -> ID.equal a' id'
        | _ -> false
      );
  *)

  type meta_vars_set = T.t MetaVar.t ID.Map.t
  (* a set of meta-variable with their reference *)

  let free_meta_vars ?(init=ID.Map.empty) ty =
    let rec aux acc ty =
      match Ty.repr ty with
      | TyI.Builtin _ | TyI.Const _ -> acc
      | TyI.Var v ->
          aux acc (Var.ty v) (* type can also contain metas *)
      | TyI.Meta var ->
          assert (MetaVar.can_bind var);
          ID.Map.add (MetaVar.id var) var acc
      | TyI.App (f,l) ->
          let acc = aux acc f in
          List.fold_left aux acc l
      | TyI.Arrow (a,b) ->
          let acc = aux acc a in
          aux acc b
      | TyI.Forall (v,t) ->
          (* the variable should not be a meta *)
          let acc = aux acc (Var.ty v) in
          aux acc t
    in
    aux init ty
end

