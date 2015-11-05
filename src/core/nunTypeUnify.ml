
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

module MetaVar = NunMetaVar
module ID = NunID
module Var = NunVar
module Ty = NunType_intf
module Utils = NunUtils
module Subst = Var.Subst

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

type ('t,'inv) repr = ('t,'inv) NunType_intf.repr

type 'inv_p invariant = <poly: 'inv_p; meta: NunMark.with_meta>
(** Invariant: must have meta-variables *)

exception Fail of (NunType_intf.packed * NunType_intf.packed) list * string
(** Raised when unification fails. The list of pairs of types is the
    unification stack (with the innermost types first) *)

let fpf = Format.fprintf
let spf = CCFormat.sprintf

let () = Printexc.register_printer
  (function
    | Fail (stack, msg) ->
        let pp2 out (Ty.Packed(ty1,repr1),Ty.Packed(ty2,repr2)) =
          fpf out "@[<hv2>trying to unify@ %a@ and %a@]"
            (Ty.print ~repr:repr1) ty1 (Ty.print ~repr:repr2) ty2
        in
        Some (spf "@[<hv2>unification error: %s:@ %a"
          msg (CCFormat.list pp2) stack)
    | _ -> None
  )

(* does [var] occur in [ty]? *)
let rec occur_check_
: type t inv. repr:(t,inv invariant) Ty.repr -> var:t MetaVar.t -> t -> bool
= fun ~repr ~var ty ->
  match Ty.view ~repr ty with
  | Ty.App (f, l) ->
      occur_check_ ~repr ~var f || List.exists (occur_check_ ~repr ~var) l
  | Ty.Var _ -> false (* bound var *)
  | Ty.Const _
  | Ty.Builtin _ -> false
  | Ty.Meta var' ->
      assert (MetaVar.can_bind var');
      MetaVar.equal var var'
  | Ty.Arrow (a,b) -> occur_check_ ~repr ~var a || occur_check_ ~repr ~var b
  | Ty.Forall (_,t) -> occur_check_ ~repr ~var t

(* NOTE: after dependent types are added, will need to recurse into
    types too for unification and occur-check *)

let push_ a b c = (a,b) :: c

let fail ~stack msg = raise (Fail (stack, msg))

let failf ~stack fmt =
  NunUtils.exn_ksprintf fmt
    ~f:(fun msg -> raise (Fail (stack, msg)))

let rec flatten_app_ ~repr f l = match Ty.view ~repr f with
  | Ty.App (f1, l1) -> flatten_app_ ~repr f1 (l1 @ l)
  | _ -> f, l

(* bound: set of bound variables, that cannot be unified *)
let unify_exn
: type t inv. repr:(t,inv invariant) Ty.repr -> t -> t -> unit
= fun ~repr ty1 ty2 ->
  Utils.debugf ~section 5 "@[<2>unify %a@ and %a@]"
    (fun k-> k (Ty.print ~repr) ty1 (Ty.print ~repr) ty2);
  let bound = ref Subst.empty in
  (* keep a stack of unification attempts *)
  let rec unify_ ~stack (ty1:t) ty2 =
    let stack = push_ (Ty.pack ~repr ty1) (Ty.pack ~repr ty2) stack in
    match Ty.view ~repr ty1, Ty.view ~repr ty2 with
    | Ty.Builtin s1, Ty.Builtin s2 ->
        if NunBuiltin.Ty.equal s1 s2 then ()
        else fail ~stack "incompatible symbols"
    | Ty.Const i1, Ty.Const i2 ->
        if ID.equal i1 i2 then () else fail ~stack "incompatible symbols"
    | Ty.Var v1, Ty.Var v2 when Var.equal v1 v2 -> ()
    | Ty.Var v1, Ty.Var v2 ->
        begin try
          let var = Subst.find_exn ~subst:!bound v1 in
          let var' = Subst.find_exn ~subst:!bound v2 in
          if Var.equal var var' then ()
          else failf ~stack "bound variables %a and %a are incompatible"
            Var.print v1 Var.print v2
        with Not_found ->
          fail ~stack "incompatible variables"
        end
    | Ty.Meta v1, Ty.Meta v2 when MetaVar.equal v1 v2 -> ()
    | Ty.Meta var, _ when MetaVar.can_bind var ->
        (* TODO: check that ty2 is closed! not bound vars allowed *)
        if occur_check_ ~repr ~var ty2
          then
            failf ~stack
              "cycle detected (variable %a occurs in type)" MetaVar.print var
          else MetaVar.bind ~var ty2
    | _, Ty.Meta var when MetaVar.can_bind var ->
        if occur_check_ ~repr ~var ty1
          then
            failf ~stack
              "cycle detected (variable %a occurs in type)" MetaVar.print var
          else MetaVar.bind ~var ty1
    | Ty.App (f1,l1), Ty.App (f2,l2) ->
        (* NOTE: if partial application in types is allowed,
           we must allow [length l1 <> length l2]. In that case, unification
           proceeds from the right *)
        let f1, l1 = flatten_app_ ~repr f1 l1 in
        let f2, l2 = flatten_app_ ~repr f2 l2 in
        if List.length l1<>List.length l2
          then
            failf ~stack
              "different number of arguments (%d and %d resp.)"
              (List.length l1) (List.length l2);
        unify_ ~stack f1 f2;
        List.iter2 (unify_ ~stack) l1 l2
    | Ty.Arrow (l1,r1), Ty.Arrow (l2,r2) ->
        unify_ ~stack l1 l2;
        unify_ ~stack r1 r2
    | Ty.Forall (v1,t1), Ty.Forall (v2,t2) ->
        assert (not (Subst.mem ~subst:!bound v1));
        assert (not (Subst.mem ~subst:!bound v2));
        let v = Var.make ~ty:(Var.ty v1) ~name:"?" in
        bound := Subst.add ~subst:(Subst.add ~subst:!bound v2 v) v1 v;
        unify_ ~stack t1 t2
    | Ty.Const _, _
    | Ty.Builtin _,_
    | Ty.App (_,_),_
    | Ty.Arrow (_,_),_ ->
        fail ~stack "incompatible types"
    | Ty.Var _, _ -> fail ~stack "incompatible types"
    | Ty.Forall (_,_),_ -> fail ~stack "incompatible types"
    | Ty.Meta _, _ -> fail ~stack "incompatible types"
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

type 't meta_vars_set = 't MetaVar.t ID.Map.t
(* a set of meta-variable with their reference *)

let free_meta_vars
: type t inv. repr:(t, inv invariant) repr ->
  ?init:t meta_vars_set ->
  t ->
  t meta_vars_set
= fun ~repr ?(init=ID.Map.empty) ty ->
  let rec aux acc ty =
    match Ty.view ~repr ty with
    | Ty.Builtin _ | Ty.Const _ -> acc
    | Ty.Var v ->
        aux acc (Var.ty v) (* type can also contain metas *)
    | Ty.Meta var ->
        assert (MetaVar.can_bind var);
        ID.Map.add (MetaVar.id var) var acc
    | Ty.App (f,l) ->
        let acc = aux acc f in
        List.fold_left aux acc l
    | Ty.Arrow (a,b) ->
        let acc = aux acc a in
        aux acc b
    | Ty.Forall (v,t) ->
        (* the variable should not be a meta *)
        let acc = aux acc (Var.ty v) in
        aux acc t
  in
  aux init ty


