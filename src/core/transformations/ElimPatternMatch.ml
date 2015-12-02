
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate pattern-matching in Equations and Terms} *)

module Stmt = Statement
module TI = TermMono
module TyI = TypeMono
module Subst = Var.Subst

module Make(T : TermInner.S) = struct
  module U = TermInner.Util(T)
  module P = TermInner.Print(T)
  module TMono = TermMono.Make(T)
  module TyMono = TypeMono.Make(T)

  type term = T.t

  let mk_select_ c i t = U.app_builtin (`DataSelect(c,i)) [t]
  let mk_test_ c t = U.app_builtin (`DataTest c) [t]
  let mk_ite_ a b c = U.app_builtin `Ite [a;b;c]

  (* apply substitution [ctx.subst] in [t], and also replace pattern matching
     with [`DataSelect] and [`DataTest] *)
  let rec elim_match_ ~subst t = match TMono.repr t with
    | TI.Var v ->
        CCOpt.get t (Subst.find ~subst v)
    | TI.Const _ -> t
    | TI.App (f,l) -> U.app (elim_match_ ~subst f) (elim_match_l_ ~subst l)
    | TI.AppBuiltin (b,l) -> U.app_builtin b (elim_match_l_ ~subst l)
    | TI.Bind ((`Forall | `Exists | `Fun) as b,v,t) ->
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (U.var v') in
        let t' = elim_match_ ~subst t in
        U.mk_bind b v' t'
    | TI.Let (v,t,u) ->
        let t' = elim_match_ ~subst t in
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (U.var v') in
        U.let_ v' t' (elim_match_ ~subst u)
    | TI.TyBuiltin _ -> t
    | TI.TyArrow (a,b) ->
        U.ty_arrow (elim_match_ ~subst a)(elim_match_ ~subst b)
    | TI.Match (t,l) ->
        (* change t into t';
            then a decision tree is built where
              each case   [c,vars,rhs] is changed into:
              "if is-c t' then rhs[vars_i := select-c-i t'] else ..."
        *)
        let t' = elim_match_ ~subst t in
        (* remove first binding to make it the default case *)
        let c1, (vars1,rhs1) = ID.Map.choose l in
        let subst1 = CCList.Idx.foldi
          (fun subst i vi -> Subst.add ~subst vi (mk_select_ c1 i t'))
          subst vars1
        in
        let default_case = elim_match_ ~subst:subst1 rhs1 in
        (* series of ite with selectors on the other cases *)
        let l = ID.Map.remove c1 l in
        ID.Map.fold
          (fun c (vars,rhs) acc ->
            let subst' = CCList.Idx.foldi
              (fun subst i vi -> Subst.add ~subst vi (mk_select_ c i t'))
              subst vars
            in
            let rhs' = elim_match_ ~subst:subst' rhs in
            mk_ite_ (mk_test_ c t') rhs' acc
          )
          l
          default_case

  and elim_match_l_ ~subst l =
    List.map (elim_match_ ~subst) l

  let elim_match t = elim_match_ ~subst:Subst.empty t

  let tr_problem pb =
    Problem.map pb
      ~term:elim_match
      ~ty:elim_match

  let pipe ~print =
    let open Transform in
    let on_encoded =
      if print then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of pattern-match: %a@]@." PPb.print]
      else [] in
    let encode pb = tr_problem pb, () in
    make1 ~name:"elim_match"
      ~encode
      ~on_encoded
      ~decode:(fun () x -> x)
      ()
end
