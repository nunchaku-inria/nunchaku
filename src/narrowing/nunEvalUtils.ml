
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Utils: reduction, unification, etc.} *)

module ID = NunID
module Var = NunVar
module Env = NunEnv
module Subst = Var.Subst
module DBEnv = NunDBEnv
module T = NunTermEval
module VarSet = T.VarSet

exception NotEnoughArguments

(* take exactly [n] elements of [l], and returns the remaining ones too
   @raise NotEnoughArguments if [length l < n] *)
let rec split_n_ n l = match l with
  | _ when n=0 -> [], l
  | x :: l' ->
      let l1, l2 = split_n_ (n-1) l' in
      x :: l1, l2
  | [] -> raise NotEnoughArguments

(* XXX: whnf will not deal with boolean operators or binders, because it
   does not evaluate under them. *)

(* compute the weak-head normal form *)
let rec whnf
: subst:T.subst -> T.TermTop.t -> T.TermTop.t
= fun ~subst top ->
  let open T.TermTop in
  match top.cont, top.head with
  | _, (T.App _ | T.Ite _ | T.Match _) -> assert false (* invariant *)
  | _, T.DB v when v.T.DB.index < DBEnv.length top.env ->
      let n = v.T.DB.index in
      begin match DBEnv.nth top.env n with
        | T.Local_decl _ -> top (* not bound *)
        | T.Local_def (_, lazy t') ->
            (* [v] is bound to [t'], so replace it. Lifting is need in
              case [t'] is not closed. *)
            let t' = T.db_lift n t' in
            whnf ~subst (T.TermTop.set_head top ~hd:t')
      end
  | _, T.Meta v ->
      begin match Subst.find ~subst v with
      | None -> top  (* blocked *)
      | Some t' ->
          assert (T.db_closed t');
          whnf ~subst (T.TermTop.set_head top ~hd:t')
      end
  | cont, T.Let (ty, t, u) ->
      (* evaluate [t] by need (not by value); use [lazy] to share the
          computation among all occurrences of [t] in [u] *)
      let t = lazy (T.TermTop.to_term
        (whnf ~subst (T.TermTop.of_term ~env:top.env t))
      ) in
      let env = DBEnv.cons (T.Local_def (ty, t)) top.env in
      whnf ~subst (T.TermTop.make ~cont ~env u top.args)
  | cont, T.Bind (`Fun, ty, body) ->
      begin match top.args with
      | [] -> top
      | a :: args' ->
          (* beta-reduction step: lazily evaluate the first argument (lazy
            is used to avoid recomputing it if it occurs several times
            in [body]) *)
        let a = lazy (T.TermTop.to_term (whnf ~subst a)) in
        let env = DBEnv.cons (T.Local_def (ty, a)) top.env in
        whnf ~subst (T.TermTop.make ~cont ~env body args')
      end
  | K_ite (a,_,cont), T.Builtin `True ->
      whnf ~subst (T.TermTop.set_head top ~cont ~hd:a)
  | K_ite (_,b,cont), T.Builtin `False ->
      whnf ~subst (T.TermTop.set_head top ~cont ~hd:b)
  | K_ite _, _ ->
      top (* blocked, for now *)
  | K_match (l, cont), T.Const c ->
      begin match c.T.const_def with
      | T.Opaque
      | T.Datatype _ -> top
      | T.Def t' ->
          whnf ~subst (T.TermTop.set_head top ~hd:t')
      | T.Cstor _ ->
          (* constructor applied to arguments; if enough arguments, we can
             reduce to the proper branch (after pushing arguments in the env) *)
          begin try
            let tys, rhs = ID.Map.find c.T.const_id l in
            (*
               - push [c_args], the arguments of the constructor
                 into the environment
               - remove [c_args] from the stack, obtaining [args']
            *)
            let len = DBEnv.length tys in
            let c_args, args' = split_n_ len top.args in
            let env = push_top_defs_ ~subst (DBEnv.to_list tys) c_args top.env in
            whnf ~subst (T.TermTop.make ~cont ~env rhs args')
          with
          | Not_found -> assert false  (* ill-typed matching: wrong constructor *)
          | NotEnoughArguments -> top (* constructor partially applied *)
          end
      end
  | K_match _, _ -> top
  | _, T.Const c ->
      begin match c.T.const_def with
      | T.Datatype _
      | T.Opaque
      | T.Cstor _ -> top  (* normal form *)
      | T.Def t' ->
          whnf ~subst (T.TermTop.set_head top ~hd:t')
      end
  | _, (T.DB _ | T.Bind _ | T.Builtin _ | T.TyArrow _) -> top

(* [types -> topterm list -> env -> env]
   push terms as definitions in the environment *)
and push_top_defs_ ~subst tys l env = match tys, l with
  | [], [] -> env
  | [], _ | _, [] -> assert false
  | ty :: tys', t :: l' ->
      let env = push_top_defs_ ~subst tys' l' env in
      (* we want to evaluate [t'] only once, so we use [lazy] to
        memoize its normalized form *)
      let t' = lazy (T.TermTop.to_term (whnf ~subst t)) in
      DBEnv.cons (T.Local_def (ty, t')) env


