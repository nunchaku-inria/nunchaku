
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate pattern-matching in Equations and Terms} *)

open Nunchaku_core

module Stmt = Statement
module TI = TermInner
module Subst = Var.Subst
module T = Term

let name = "elim_match"

type term = T.t

type mode =
  | Elim_data_match
  | Elim_codata_match
  | Elim_both

let pp_mode out = function
  | Elim_data_match -> CCFormat.string out "elim_data_match"
  | Elim_codata_match -> CCFormat.string out "elim_codata_match"
  | Elim_both -> CCFormat.string out "elim_both"

let mk_select_ = T.data_select
let mk_test_ = T.data_test

(* apply substitution [ctx.subst] in [t], and also replace pattern matching
   with [`DataSelect] and [`DataTest] *)
let elim_match ~mode ~env t =
  let open Binder in
  (* should we encode a match on this term? Depends on [mode] and its type *)
  let should_encode t =
    let ty = T.ty_exn ~env t in
    let info = T.info_of_ty_exn ~env ty in
    match mode, Env.def info with
      | Elim_both, _ -> true
      | Elim_data_match, Env.Data (`Data,_,_)
      | Elim_codata_match, Env.Data (`Codata,_,_) -> true
      | _, Env.Data (_,_,_) -> false
      | _ -> assert false
  in
  let rec elim_match_ ~subst t = match T.repr t with
    | TI.Var v ->
      CCOption.get_or ~default:t (Subst.find ~subst v)
    | TI.Const _ -> t
    | TI.App (f,l) -> T.app (elim_match_ ~subst f) (elim_match_l_ ~subst l)
    | TI.Builtin b -> T.builtin (Builtin.map b ~f:(elim_match_ ~subst))
    | TI.Bind ((Forall | Exists | Fun | Mu) as b,v,t) ->
      let v' = Var.fresh_copy v in
      let subst = Subst.add ~subst v (T.var v') in
      let t' = elim_match_ ~subst t in
      T.mk_bind b v' t'
    | TI.Bind (TyForall, _, _) | TI.TyMeta _ -> assert false (* by precond *)
    | TI.Let (v,t,u) ->
      let t' = elim_match_ ~subst t in
      let v' = Var.fresh_copy v in
      let subst = Subst.add ~subst v (T.var v') in
      T.let_ v' t' (elim_match_ ~subst u)
    | TI.TyBuiltin _ -> t
    | TI.TyArrow (a,b) ->
      T.ty_arrow (elim_match_ ~subst a)(elim_match_ ~subst b)
    | TI.Match (t,l,def) when should_encode t ->
      (* change t into t';
         then a decision tree is built where
          each case  [c,vars,rhs] is changed into:
          "if is-c t' then rhs[vars_i := select-c-i t'] else ..."
      *)
      let t' = elim_match_ ~subst t in
      (* get a default case (last leaf of the decision tree) *)
      let l, default_case = match def with
        | Some (rhs,_) ->
          l, elim_match_ ~subst rhs
        | None ->
          (* remove first binding to make it the default case *)
          let c1, (_, vars1,rhs1) = ID.Map.choose l in
          let subst0 = CCList.foldi
              (fun subst i vi -> Subst.add ~subst vi (mk_select_ c1 i t'))
              subst vars1
          in
          let default_case = elim_match_ ~subst:subst0 rhs1 in
          let l = ID.Map.remove c1 l in
          l, default_case
      in
      (* series of ite with selectors on the other cases *)
      ID.Map.fold
        (fun c (_, vars,rhs) acc ->
           let subst' = CCList.foldi
               (fun subst i vi -> Subst.add ~subst vi (mk_select_ c i t'))
               subst vars
           in
           let rhs' = elim_match_ ~subst:subst' rhs in
           T.ite (mk_test_ c t') rhs' acc)
        l
        default_case
    | TI.Match (t, l, def) ->
      let t = elim_match_ ~subst t in
      let def = TermInner.map_default_case (elim_match_ ~subst) def in
      let l =
        ID.Map.map
          (fun (tys, vars,rhs) ->
             let subst, vars = CCList.fold_map T.rename_var subst vars in
             tys, vars, elim_match_ ~subst rhs)
          l
      in
      T.match_with t l ~def

  and elim_match_l_ ~subst l =
    List.map (elim_match_ ~subst) l
  in
  elim_match_ ~subst:Subst.empty t

let tr_problem ?(mode=Elim_both) pb =
  let env = Problem.env pb in
  Problem.map pb
    ~term:(elim_match ~env ~mode)
    ~ty:(fun ty->ty)

let pipe ~mode ~print ~check =
  let open Transform in
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.P in
      Format.printf "@[<v2>@{<Yellow>after elimination of pattern-match@}: %a@]@." PPb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.check_problem (C.empty ()))
  in
  let encode pb = tr_problem ~mode pb, () in
  make ~name
    ~encode
    ~input_spec:Transform.Features.(empty |> update Ty Mono)
    ~map_spec:Transform.Features.(update Match Absent)
    ~on_encoded
    ~decode:(fun () x -> x)
    ()
