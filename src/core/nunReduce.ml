
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Var = NunVar
module TI = NunTerm_intf

module Make(T : NunTerm_ho.S)(Subst : Var.SUBST with type ty = T.ty) = struct
  (* utils *)
  module U = NunTerm_ho.SubstUtil(T)(Subst)

  (* low level implementation *)
  module Full = struct
    type subst = T.ty Subst.t

    (* head applied to args, in environment subst *)
    type state = {
      head: T.t;
      args: T.t list;
      subst: subst;
    }

    let push_args ~st l = l @ st.args

    (* convert a state back to a term *)
    let term_of_state st =
      let head = U.eval ~subst:st.subst st.head in
      match st.args with
        | [] -> head
        | l ->
            let l = List.map (U.eval ~subst:st.subst) l in
            T.app head l

    (* reduce until the head is not a function *)
    let rec whnf_ st = match T.view st.head with
      | TI.Const _
      | TI.Builtin _ -> st
      | TI.Var v ->
          (* dereference, if any *)
          begin match Subst.find ~subst:st.subst v with
          | None -> st
          | Some t -> whnf_ {st with head=t}
          end
      | TI.App (f, l) ->
          whnf_ {st with head=f; args=push_args ~st l}
      | TI.Fun (v,body) ->
          begin match st.args with
          | [] -> st
          | a :: args' ->
              (* beta-redex *)
              whnf_ {
                head=body;
                args=args';
                subst=Subst.add ~subst:st.subst v a
              }
          end
      | TI.Eq _
      | TI.Forall _
      | TI.Exists _
      | TI.Let _
      | TI.Ite _
      | TI.TyKind
      | TI.TyType
      | TI.TyBuiltin _
      | TI.TyArrow _
      | TI.TyForall _ -> st
      | TI.TyMeta _ -> assert false

    let whnf ?(subst=Subst.empty) t args =
      let st = whnf_ {head=t; args; subst; } in
      st.head, st.args, st.subst

    (* strong normal form *)
    let rec snf_ st =
      (* first, head reduction *)
      let st = whnf_ st in
      (* then, reduce subterms *)
      match T.view st.head with
      | TI.TyKind
      | TI.TyType
      | TI.TyBuiltin _
      | TI.Const _
      | TI.Builtin _ ->
          (* TODO: reduce boolean expressions? *)
          st
      | TI.TyForall (_,_)
      | TI.TyArrow (_,_) ->
          st (* NOTE: depend types might require beta-reduction in types *)
      | TI.Var v ->
          assert (not (Subst.mem ~subst:st.subst v));
          st
      | TI.App (_,_) -> assert false  (* not WHNF *)
      | TI.Fun (v, body) ->
          assert (st.args = []);
          enter_snf_ st v body (fun v body -> T.fun_ v body)
      | TI.Forall (v,t) ->
          enter_snf_ st v t (fun v t -> T.forall v t)
      | TI.Exists (v,t) ->
          enter_snf_ st v t (fun v t -> T.exists v t)
      | TI.Let (v,t,u) ->
          let t = snf_term ~subst:st.subst t in
          enter_snf_ st v u (fun v u -> T.let_ v t u)
      | TI.Ite (a,b,c) ->
          (* XXX: should we check [a] against [true] or [false]? *)
          {st with head=
            T.ite
              (snf_term ~subst:st.subst a)
              (snf_term ~subst:st.subst b)
              (snf_term ~subst:st.subst c)
          }
      | TI.Eq (a,b) ->
          { st with head=T.eq (snf_term ~subst:st.subst a) (snf_term ~subst:st.subst b) }
      | TI.TyMeta _ -> assert false

    (* compute the SNF of this term in [subst] *)
    and snf_term ~subst t = term_of_state (snf_ {head=t; subst; args=[]})

    (* enter the scope of [v] and compute [snf t] *)
    and enter_snf_ st v t f =
      let v' = Var.fresh_copy v in
      let head = snf_term t ~subst:(Subst.add ~subst:st.subst v (T.var v')) in
      {st with head=f v' head; }
  end

  (* NOTE: when dependent types are added, substitution in types is needed *)

  (** {6 Reduction State} *)

  let whnf t =
    let st = Full.whnf_ {Full.subst=Subst.empty; head=t; args=[]} in
    Full.term_of_state st

  let snf t =
    let st = Full.snf_ {Full.subst=Subst.empty; head=t; args=[]} in
    Full.term_of_state st
end




