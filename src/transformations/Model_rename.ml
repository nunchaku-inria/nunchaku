
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Rename values in a model} *)

open Nunchaku_core

module TI = TermInner
module DT = Model.DT
module T = TermInner.Default
module U = T.U
module Ty = TypeMono.Make(T)
module Red = Reduce.Make(T)

let fpf = Format.fprintf
let name = "model_rename"
let section = Utils.Section.(make ~parent:root) name

(* a kind of flat-form printing of [t] *)
let rec flatten_ty out t = match T.repr t with
  | TI.App (f,l) ->
      fpf out "%a_%a"
        flatten_ty f
        CCFormat.(list ~start:"" ~stop:"" ~sep:"_" flatten_ty) l
  | TI.Const id -> ID.print_name out id
  | TI.TyBuiltin b -> CCFormat.string out (TI.TyBuiltin.to_string b)
  | _ -> ()

(* return a prefix for constants in the domain of this given type *)
let pick_prefix_ ty = CCFormat.sprintf "@[<h>%a@]" flatten_ty ty

(* compute a set of renaming rules for the model [m] *)
let renaming_rules_of_model_ m =
  List.fold_left
    (fun acc (t, dom) ->
      let prefix = pick_prefix_ t in
      CCList.Idx.foldi
        (fun acc i id ->
          let name = CCFormat.sprintf "$%s_%d" prefix i in
          let rhs = ID.make name in
          ID.Map.add id rhs acc)
        acc dom)
    ID.Map.empty
    m.Model.finite_types

let pp_rule_ out (l,r) =
  fpf out "%a → @[%a@]" ID.print l ID.print r

(* rename [v] and add the renaming to [subst] *)
let rename_copy_ subst v =
  let name = Format.sprintf "v_%d" (Var.Subst.size subst) in
  let v' = Var.make ~ty:(Var.ty v) ~name in
  Var.Subst.add ~subst v v', v'

(* rewrite [t] using the set of rewrite rules *)
let rec rewrite_term_ rules subst t =
  match T.repr t with
  | TI.Const id ->
      begin try
        let id' = ID.Map.find id rules in
        U.const id'
      with Not_found -> t
      end
  | TI.Var v ->
      begin try U.var (Var.Subst.find_exn ~subst v)
      with Not_found -> t
      end
  | _ ->
      let t =
        U.map subst t
          ~f:(rewrite_term_ rules)
          ~bind:rename_copy_
      in
      (* reduce the term *)
      Red.whnf t

let rename m =
  let rules = renaming_rules_of_model_ m in
  Utils.debugf 5 ~section "@[<2>apply rewrite rules@ @[<v>%a@]@]"
    (fun k->k (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_rule_) (ID.Map.to_seq rules));
  (* update domains *)
  let finite_types =
    let rename_id id =
      try ID.Map.find id rules
      with Not_found -> id
    in
    List.map
      (fun (t, dom) -> t, List.map rename_id dom)
      m.Model.finite_types
  in
  (* rewrite every term *)
  let rw_nil = rewrite_term_ rules Var.Subst.empty in
  { m with Model.
    finite_types;
    constants=List.map
      (fun (t,u,k) -> rw_nil t, rw_nil u, k)
      m.Model.constants;
    funs=List.map
      (fun (t,vars,rhs, k) ->
        let t = rw_nil t in
        let subst, vars = Utils.fold_map rename_copy_ Var.Subst.empty vars in
        let rw_subst t = rewrite_term_ rules subst t in
        t, vars, DT.map ~var:(Var.Subst.find ~subst) ~term:rw_subst ~ty:rw_subst rhs, k)
      m.Model.funs;
  }

let pipe_rename ~print:must_print =
  Transform.backward ~name
    (fun res ->
      let res' = Problem.Res.map_m ~f:rename res in
      if must_print then (
        let module P = TI.Print(T) in
        Format.printf "@[<v2>@{<Yellow>after model renaming@}:@ %a@]@."
          (Problem.Res.print P.print P.print) res');
      res')
