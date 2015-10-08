
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Var = NunVar
module TI = NunTerm_intf

module Make(T : NunTerm_ho.S) = struct
  (* environment for reduction *)
  module Env = struct
    module M = Map.Make(struct
      type t = T.Ty.t Var.t
      let compare = Var.compare
    end)

    type t = T.t M.t

    let empty = M.empty

    let add ~env v t = M.add v t env

    let mem ~env v = M.mem v env

    let find ~env v = M.find v env
  end

  (* NOTE: when dependent types are added, substitution in types is needed *)

  (* apply substitution to [t] *)
  let rec apply_subst ~env t =
    match T.view t with
    | TI.Var v ->
        begin try Env.find ~env v
        with Not_found -> t
        end
    | TI.Const _ -> t
    | TI.TyBuiltin _
    | TI.TyKind
    | TI.TyType
    | TI.Builtin _ -> t
    | TI.App (f,l) ->
        T.app (apply_subst ~env f) (List.map (apply_subst ~env) l)
    | TI.Eq (a,b) -> T.eq (apply_subst ~env a)(apply_subst ~env b)
    | TI.Fun (v,body) ->
        enter_ ~env v
          (fun ~env v' ->
            let body = apply_subst ~env body in
            T.fun_ v' body
          )
    | TI.Forall (v,t) ->
        enter_ ~env v
          (fun ~env v' ->
            let t = apply_subst ~env t in
            T.forall v' t
          )
    | TI.Exists (v,t) ->
        enter_ ~env v
          (fun ~env v' ->
            let t = apply_subst ~env t in
            T.exists v' t
          )
    | TI.Let (v,t,u) ->
        let t = apply_subst ~env t in
        let v' = Var.fresh_update_ty v ~f:(apply_subst ~env) in
        let env = Env.add ~env v (T.var v') in
        let u = apply_subst ~env u in
        T.let_ v' t u
    | TI.Ite (a,b,c) ->
        T.ite (apply_subst ~env a)(apply_subst ~env b)(apply_subst ~env c)
    | TI.TyArrow (a,b) ->
        T.ty_arrow (apply_subst ~env a) (apply_subst ~env b)
    | TI.TyForall (v,t) ->
        enter_ ~env v
          (fun ~env v' ->
            let t = apply_subst ~env t in
            T.ty_forall v' t
          )
    | TI.TyMeta _ -> assert false

  (* enter the scope where [v : ty] *)
  and enter_ ~env v f =
    let v' = Var.fresh_update_ty v ~f:(apply_subst ~env) in
    let env = Env.add ~env v (T.var v') in
    f ~env v'

  (** {6 Reduction State} *)

  (* head applied to args, in environment env *)
  type state = {
    head: T.t;
    args: state list;
    env: Env.t;
  }

  let st_of_term ?(env=Env.empty) head = {head;env;args=[]}

  let push_args ~st l = List.map (st_of_term ~env:st.env) l @ st.args

  (* convert a state back to a term *)
  let rec term_of_state st =
    let head = apply_subst ~env:st.env st.head in
    match st.args with
      | [] -> head
      | l ->
          let l = List.map term_of_state l in
          T.app head l

  (* reduce until the head is not a function *)
  let rec whnf_ st = match T.view st.head with
    | TI.Const _
    | TI.Builtin _ -> st
    | TI.Var v ->
        (* dereference, if any *)
        begin try
          let t = Env.find ~env:st.env v in
          whnf_ {st with head=t}
        with Not_found -> st
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
              env=Env.add ~env:st.env v (term_of_state a)
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

  let whnf t =
    let st = whnf_ {env=Env.empty; head=t; args=[]} in
    term_of_state st

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
        assert (not (Env.mem ~env:st.env v));
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
        let t = snf_term ~env:st.env t in
        enter_snf_ st v u (fun v u -> T.let_ v t u)
    | TI.Ite (a,b,c) ->
        (* XXX: should we check [a] against [true] or [false]? *)
        {st with head=
          T.ite
            (snf_term ~env:st.env a)
            (snf_term ~env:st.env b)
            (snf_term ~env:st.env c)
        }
    | TI.Eq (a,b) ->
        { st with head=T.eq (snf_term ~env:st.env a) (snf_term ~env:st.env b) }
    | TI.TyMeta _ -> assert false

  (* compute the SNF of this term in [env] *)
  and snf_term ~env t = term_of_state (snf_ {head=t; env; args=[]})

  (* enter the scope of [v] and compute [snf t] *)
  and enter_snf_ st v t f =
    let v' = Var.fresh_copy v in
    let head = snf_term t ~env:(Env.add ~env:st.env v (T.var v')) in
    {st with head=f v' head; }

  let snf t =
    let st = snf_ {env=Env.empty; head=t; args=[]} in
    term_of_state st
end




