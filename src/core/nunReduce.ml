
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Var = NunVar
module TI = NunTerm_intf

(* TODO put the signature elsewhere *)
module Make(T : NunTypeInference.TERM) = struct
  (* environment for reduction *)
  type env = T.t Var.Map.t

  let empty_env = Var.Map.empty

  (* NOTE: when dependent types are added, substitution in types is needed *)

  let get_ty_ t = match T.ty t with Some x->x | None -> assert false

  (* apply substitution to [t] *)
  let rec apply_subst ~env t =
    match T.view t with
    | TI.Var v ->
        begin try Var.Map.find v env
        with Not_found -> t
        end
    | TI.TyMeta (_,_)
    | TI.TyBuiltin _
    | TI.TyKind
    | TI.TyType
    | TI.Builtin _ -> t
    | TI.App (f,l) ->
        let ty = apply_subst_ty ~env (get_ty_ t) in
        T.app ~ty (apply_subst ~env f) (List.map (apply_subst ~env) l)
    | TI.Fun (v,ty_arg,body) ->
        let ty = apply_subst_ty ~env (get_ty_ t) in
        enter_ ~env v ty_arg
          (fun ~env v' ty_arg' ->
            let body = apply_subst ~env body in
            T.fun_ ~ty v' ~ty_arg:ty_arg' body
          )
    | TI.Forall (v,ty_arg,t) ->
        enter_ ~env v ty_arg
          (fun ~env v' ty_arg' ->
            let t = apply_subst ~env t in
            T.forall v' ~ty_arg:ty_arg' t
          )
    | TI.Exists (v,ty_arg,t) ->
        enter_ ~env v ty_arg
          (fun ~env v' ty_arg' ->
            let t = apply_subst ~env t in
            T.exists v' ~ty_arg:ty_arg' t
          )
    | TI.Let (v,t,u) ->
        let t = apply_subst ~env t in
        let v' = Var.fresh_copy v in
        let env = Var.Map.add v (T.var ~ty:(get_ty_ t) v') env in
        let u = apply_subst ~env u in
        T.let_ v' t u
    | TI.TyArrow (a,b) ->
        T.Ty.to_term (T.ty_arrow (apply_subst_ty ~env a) (apply_subst_ty ~env b))
    | TI.TyForall (v,t) ->
        enter_ ~env v T.ty_type
          (fun ~env v' _ ->
            let t = apply_subst_ty ~env t in
            T.Ty.to_term (T.ty_forall v' t)
          )

  and apply_subst_ty ~env (ty:T.Ty.t) =
    T.Ty.of_term_exn (apply_subst ~env (ty:>T.t))

  (* enter the scope where [v : ty] *)
  and enter_ ~env v ty f =
    let ty = apply_subst_ty ~env ty in
    let v' = Var.fresh_copy v in
    let env = Var.Map.add v (T.var ~ty v') env in
    f ~env v' ty

  (** {6 Reduction State} *)

  (* head applied to args, in environment env *)
  type state = {
    head: T.t;
    args: state list;
    env: env;
  }

  let st_of_term ?(env=empty_env) head = {head;env;args=[]}

  let push_args ~st l = List.map (st_of_term ~env:st.env) l @ st.args

  (* convert a state back to a term *)
  let rec term_of_state st =
    let head = apply_subst ~env:st.env st.head in
    match st.args with
      | [] -> head
      | l ->
          let l = List.map term_of_state l in
          T.build (TI.App(head, l))

  (* reduce until the head is not a function *)
  let rec whnf_ st = match T.view st.head with
    | TI.Builtin _ -> st
    | TI.Var v ->
        (* dereference, if any *)
        begin try
          let t = Var.Map.find v st.env in
          whnf_ {st with head=t}
        with Not_found -> st
        end
    | TI.App (f, l) ->
        whnf_ {st with head=f; args=push_args ~st l}
    | TI.Fun (v,_ty,body) ->
        begin match st.args with
        | [] -> st
        | a :: args' ->
            (* beta-redex *)
            whnf_ {
              head=body;
              args=args';
              env=Var.Map.add v (term_of_state a) st.env
            }
        end
    | TI.Forall _
    | TI.Exists (_,_,_)
    | TI.Let (_,_,_)
    | TI.TyKind
    | TI.TyType
    | TI.TyMeta (_,_)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_)
    | TI.TyForall (_,_) -> st

  let whnf t =
    let st = whnf_ {env=empty_env; head=t; args=[]} in
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
    | TI.Builtin _
    | TI.TyMeta (_,_) -> st
    | TI.TyForall (_,_)
    | TI.TyArrow (_,_) ->
        st (* NOTE: depend types might require beta-reduction in types *)
    | TI.Var v ->
        assert (not (Var.Map.mem v st.env));
        st
    | TI.App (_,_) -> assert false  (* not WHNF *)
    | TI.Fun (v, ty_arg, body) ->
        assert (st.args = []);
        let ty = get_ty_ st.head in
        enter_snf_ st v ty_arg body (fun v body -> T.fun_ ~ty v ~ty_arg body)
    | TI.Forall (v,ty_arg,t) ->
        enter_snf_ st v ty_arg t (fun v t -> T.forall v ~ty_arg t)
    | TI.Exists (v,ty_arg,t) ->
        enter_snf_ st v ty_arg t (fun v t -> T.exists v ~ty_arg t)
    | TI.Let (v,t,u) ->
        let t = snf_term ~env:st.env t in
        enter_snf_ st v (get_ty_ t) u (fun v u -> T.let_ v t u)

  (* compute the SNF of this term in [env] *)
  and snf_term ~env t = term_of_state (snf_ {head=t; env; args=[]})

  (* enter the scope of [v] and compute [snf t] *)
  and enter_snf_ st v ty_v t f =
    let v' = Var.fresh_copy v in
    let head = snf_term t ~env:(Var.Map.add v (T.var ~ty:ty_v v') st.env) in
    {st with head=f v' head; }

  let snf t =
    let st = snf_ {env=empty_env; head=t; args=[]} in
    term_of_state st
end




