
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Conversion from {!NunTermTyped} to {!NunANF}

  Types are useful for introducing intermediate variables
  that will stand for sub-expressions. *)

module ID = NunID
module Var = NunVar
module Subst = Var.Subst
module Stmt = NunStatement
module T = NunTermEval
module DBEnv = NunDBEnv
module Env = NunEvalEnv
module Const = NunEvalConst

exception InvalidProblem of string
(** Raised when a problem cannot be converted into a narrowing problem *)

let section = NunUtils.Section.make "eval_of_poly"

let () = Printexc.register_printer
  (function
    | InvalidProblem msg -> Some ("invalid problem for narrowing: " ^ msg)
    | _ -> None
  )

module Convert(T1 : NunTermInner.REPR) : sig
  val convert_pb: (T1.t, T1.t, <eqn:[`Single];..>) NunProblem.t -> Env.t * T.term
  (** [convert_pb pb] returns a pair [env, goal] where [goal] is the goal
    of [pb] after conversion into ANF, and [env] is an environment suitable
    for evaluation.
    @raise InvalidProblem if the translation fails. *)
end = struct
  module TI = NunTermInner
  module P = NunTermInner.Print(T1)
  module U = NunTermTyped.Util

  let invalid_pb msg = raise (InvalidProblem msg)
  let invalid_pbf fmt = NunUtils.exn_ksprintf fmt ~f:invalid_pb

  module VarSet = T.VarSet

  type ctx = {
    env: Env.t; (* global env *)
    bound: T.ty DBEnv.t; (* environment under binders *)
    vars: (T1.t, int) Subst.t; (* variable -> de Bruijn level *)
  }

  (* ty: the type of [v] after translation *)
  let push_var ~ctx v ty level = {ctx with
    bound=DBEnv.cons ty ctx.bound;
    vars=Subst.add ~subst:ctx.vars v level;
  }

  let debug_declare_ c =
    NunUtils.debugf ~section 5 "@[declare %a@]"
      (fun k -> k (Const.print_full T.Print.print) c)

  let rec push_vars ~ctx vars tys level = match vars, tys with
    | [], [] -> ctx, level
    | [], _ | _, [] -> assert false
    | v :: vars', ty::tys' ->
        let ctx, level' = push_vars ~ctx vars' tys' level in
        push_var ~ctx v ty level', level' + 1

  let find_var_ ~ctx v =
    match Subst.find ~subst:ctx.vars v with
      | None -> invalid_pbf "variable %a not bound" Var.print v
      | Some l -> l

  let find_id_ ~ctx id =
    try Env.find_exn ~env:ctx.env id
    with Not_found -> invalid_pbf "identifier %a not defined" ID.print_name id

  let rec into_term ~ctx t : T.term = match T1.repr t with
    | TI.Var v ->
        let lev = find_var_ ~ctx v in
        let cur_lev = DBEnv.length ctx.bound in
        let n = cur_lev - lev - 1 in
        (* FIXME: if not bound, make it a meta? *)
        NunUtils.debugf ~section 5 "variable %a / %d with env of size %d"
          (fun k ->k Var.print v n cur_lev);
        let ty = DBEnv.nth ctx.bound n in
        T.db (T.DB.make ~name:(Var.name v) ~ty n)
    | TI.Const id -> T.const (find_id_ ~ctx id)
    | TI.App (f, []) -> into_term ~ctx f
    | TI.App (f, l) ->
        let f = into_term ~ctx f in
        let l = into_term_l ~ctx l in
        T.app f l
    | TI.AppBuiltin (`Ite, [a;b;c]) ->
        T.ite (into_term ~ctx a)(into_term ~ctx b)(into_term ~ctx c)
    | TI.AppBuiltin ((`DataSelect _ | `DataTest _), _) ->
        NunUtils.not_implemented "builtins dataselect/test" (* TODO *)
    | TI.AppBuiltin (`Undefined _, _) ->
        NunUtils.not_implemented "builtins undefined" (* TODO *)
    | TI.AppBuiltin
      ((`And | `Or | `Eq | `Not | `Imply | `Equiv | `False | `True) as b,l) ->
        T.app_builtin b (into_term_l ~ctx l)
    | TI.AppBuiltin (_,_) -> assert false
    | TI.Bind (b,v,t) ->
        let lev = DBEnv.length ctx.bound in
        let ty = into_term ~ctx (Var.ty v) in
        let ctx' = push_var ~ctx v ty lev in
        T.bind b ~ty (into_term ~ctx:ctx' t)
    | TI.Let (v,t,u) ->
        let t' = into_term ~ctx t in
        let lev = DBEnv.length ctx.bound in
        let ty = into_term ~ctx (Var.ty v) in
        let ctx' = push_var ~ctx v ty lev in
        T.let_ ~ty t' (into_term ~ctx:ctx' u)
    | TI.Match (t,l) ->
        let lev = DBEnv.length ctx.bound in
        let t' = into_term ~ctx t in
        let l' = ID.Map.map
          (fun (vars,rhs) ->
            (* push variables on the stack *)
            let tys = List.map (fun v-> into_term ~ctx (Var.ty v)) vars in
            let ctx', _ = push_vars ~ctx vars tys lev in
            DBEnv.of_list tys, into_term ~ctx:ctx' rhs)
          l
        in
        T.match_ t' l'
    | TI.TyArrow (a,b) -> T.ty_arrow (into_term ~ctx a) (into_term ~ctx b)
    | TI.TyBuiltin `Type -> T.type_
    | TI.TyBuiltin `Kind -> T.kind
    | TI.TyBuiltin `Prop -> T.prop
    | TI.TyMeta _ -> assert false (* should have been inferred *)

  and into_term_l ~ctx l = List.map (into_term ~ctx) l

  let fun_into_term ~ctx vars rhs =
    let lev = DBEnv.length ctx.bound in
    (* push variables on the stack *)
    let tys = List.map (fun v-> into_term ~ctx (Var.ty v)) vars in
    let ctx', _ = push_vars ~ctx vars tys lev in
    T.fun_l tys (into_term ~ctx:ctx' rhs)

  (* convert statement and add it to [env] if it makes sense *)
  let convert_statement (env,maybe_goal) st =
    let ctx = {env; bound=DBEnv.nil; vars=Subst.empty; } in
    match Stmt.view st with
    | Stmt.Goal g ->
        begin match maybe_goal with
        | Some _ -> invalid_pb "several goals in the input"
        | None ->
            let g' = into_term ~ctx g in
            env, Some g'
        end
    | Stmt.Decl (id,_,ty) ->
        let ty = into_term ~ctx ty in
        let c = Const.make ~def:Const.Opaque ~ty id in
        debug_declare_ c;
        Env.declare ~env c, maybe_goal
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        (* symbols defined by single equations: add to definition.
         The definitions are mutually recursive, which forces us to delay
         evaluation  *)
        let rec env' = lazy (
          List.fold_left
            (fun env def ->
              let Stmt.Eqn_single (vars,rhs) = def.Stmt.rec_eqns in
              let d = def.Stmt.rec_defined in
              let ty = into_term ~ctx d.Stmt.defined_ty in
              let term = lazy (fun_into_term ~ctx:{ctx with env=Lazy.force env'} vars rhs) in
              let c = Const.make d.Stmt.defined_head ~ty ~def:(Const.Def term) in
              Env.declare ~env c
            )
            env l
          )
        in
        let env' = Lazy.force env' in
        env', maybe_goal
    | Stmt.Axiom (Stmt.Axiom_std _)
    | Stmt.Axiom (Stmt.Axiom_spec _) ->
        (* TODO: nothing? prolog defs? *)
        NunUtils.not_implemented "narrowing: cannot deal with axiom/spec"
    | Stmt.TyDef (k,l) ->
        (* declare the (co)datatypes and their constructors *)
        let env = List.fold_left
          (fun env tydef ->
            let ty_datatype = into_term ~ctx tydef.Stmt.ty_type in
            (* DB environment for types of the constructor *)
            let lev = DBEnv.length ctx.bound in
            let tys = List.map
              (fun v -> into_term ~ctx(Var.ty v)) tydef.Stmt.ty_vars in
            let ctx, _ = push_vars ~ctx tydef.Stmt.ty_vars tys lev in
            (* number of type variable *)
            let ty_n_vars = List.length tydef.Stmt.ty_vars in
            (* tie the knot: every constructor refers to every other constructor *)
            let rec datatype = lazy {Const.
              ty_kind=k;
              ty_id=tydef.Stmt.ty_id;
              ty_n_vars;
              ty_cstors=
                ID.Map.map
                  (fun c ->
                    let ty = into_term c.Stmt.cstor_type
                      ~ctx:{ctx with env=Lazy.force env'; } in
                    Const.make
                      c.Stmt.cstor_name
                      ~ty
                      ~def:(Const.Cstor datatype)
                  )
                  tydef.Stmt.ty_cstors;
            }
            (* environment in which the type is defined *)
            and env' = lazy (
              (* declare the type itself *)
              let c = Const.make
                tydef.Stmt.ty_id
                ~ty:ty_datatype
                ~def:(Const.Datatype datatype)
              in
              Env.declare ~env c
            ) in
            let datatype = Lazy.force datatype in
            let env' = Lazy.force env' in
            (* declare every constructor *)
            ID.Map.fold
              (fun _ c env ->
                debug_declare_ c;
                Env.declare ~env c)
              datatype.Const.ty_cstors
              env'
          )
          env l
        in
        env, maybe_goal

  let convert_pb pb =
    let env = Env.create() in
    let env, maybe_goal =
      NunProblem.statements pb
      |> CCVector.fold convert_statement (env, None)
    in
    match maybe_goal with
    | None -> invalid_pb "no goal in the input"
    | Some g -> env, g
end
