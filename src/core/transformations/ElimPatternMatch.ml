
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate pattern-matching in Equations and Terms} *)

module ID = ID
module Var = Var
module Stmt = Statement
module TI = TermMono
module TyI = TypeMono
module Subst = Var.Subst
module Env = Env

type id = ID.t

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some ("error in elim_match: " ^ msg)
    | _ -> None
  )

let error_ msg = raise (Error msg)
let errorf_ fmt = Utils.exn_ksprintf fmt ~f:(fun msg -> error_ msg)
let section = Utils.Section.make "elim_match"

module Make(T : TermInner.S) = struct
  module U = TermInner.Util(T)
  module P = TermInner.Print(T)
  module TMono = TermMono.Make(T)
  module TyMono = TypeMono.Make(T)

  type term = T.t
  type var = term Var.t
  type env = (term, term, <ty:[`Mono]; eqn:[`Linear]>) Env.t

  (* a constraint used to flatten pattern match *)
  type constraint_ =
    | EqTerm of term * term
    | Test of term * ID.t (* [t,cons] --> is_cons t *)

  let fpf = Format.fprintf

  let pp_constraint out = function
    | EqTerm (t1,t2) -> fpf out "@[<2>%a =@ %a@]" P.print t1 P.print t2
    | Test (t, id) -> fpf out "@[is-%a %a@]" ID.print_name id P.print t

  (* a local context for flattening patterns and equations *)
  type ctx = {
    env : env;
    blocked_vars: var list; (* already introduced variables *)
    c_set: constraint_ list; (* constraints *)
    subst: (term, term) Subst.t (* substitution to apply to RHS *)
  }

  let empty_ctx ~env = { blocked_vars=[]; c_set=[]; subst=Subst.empty; env; }

  let add_constr_ ~ctx c =
    Utils.debugf ~section 4 "add constraint %a" (fun k-> k pp_constraint c);
    {ctx with c_set=c::ctx.c_set; }

  let add_subst_ ~ctx v t =
    Utils.debugf ~section 4 "add binding %a -> `%a`"
      (fun k-> k Var.print v P.print t);
    {ctx with subst=Subst.add ~subst:ctx.subst v t;}

  let add_var_ ~ctx v =
    Utils.debugf ~section 4 "block var %a" (fun k-> k Var.print v);
    {ctx with blocked_vars=v::ctx.blocked_vars; }

  let mk_data_select_ a ~id i = U.app_builtin (`DataSelect (id,i)) [a]
  let mk_data_test_ a ~id = U.app_builtin (`DataTest id) [a]

  let find_ty_ ~env id = match Env.find_ty ~env id with
    | Some t -> t
    | None -> errorf_ "could not find the type of %a" ID.print_name id

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match TyMono.repr ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

  (* [v] already used in the pattern? *)
  let blocked_var_ ~ctx v = List.exists (Var.equal v) ctx.blocked_vars

  (* add enough constraints for making [t], a sub-pattern, equal to
     the term [to_].
     Returns a context updated with the necessary substitutions and constraints *)
  let rec mk_eq ~ctx ~to_ t =
    let t = U.deref ~subst:ctx.subst t in
    match TMono.repr t with
    | TI.Var v ->
        assert (not (Subst.mem ~subst:ctx.subst v));
        if blocked_var_ ~ctx v
        then add_constr_ ~ctx (EqTerm (t, to_)) (* variable already bound *)
        else add_subst_ ~ctx v to_ (* TODO: occur check? *)
    | TI.Const id -> mk_eq_constr ~ctx ~to_ id []
    | TI.App (f, l) ->
        (* we only deal with [constructor l] *)
        begin match TMono.repr f with
        | TI.Const id -> mk_eq_constr ~ctx ~to_ id l
        | _ -> errorf_ "expected first-order pattern, got %a" P.print t
        end
    | TI.AppBuiltin (_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_) ->
        Utils.not_implemented "flatten equation: non inductive pattern on LHS"
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> errorf_ "expected pattern, got type %a" P.print t
    | TI.Bind (_,_,_) -> errorf_ "expected pattern, got %a" P.print t

  and mk_eq_constr ~ctx ~to_ id l =
    (* find the declaration/definition of [id] *)
    let info =
      try Env.find_exn ~env:ctx.env id
      with Not_found ->
        errorf_ "could not find definition for %a" ID.print_name id
    in
    (* it must be (co)inductive (for now) *)
    match info.Env.def with
    | Env.Cstor (_, _, _, cstor) ->
        (* we have [c l_1...l_n], ensure that [to_ = c to_1...to_n]
            and that [l_i = to_i] *)
        assert (List.length l = List.length cstor.Stmt.cstor_args);
        assert (ID.equal id cstor.Stmt.cstor_name);
        let ctx = add_constr_ ~ctx (Test (to_, id)) in
        CCList.Idx.foldi
          (fun ctx i li -> mk_eq ~ctx li ~to_:(mk_data_select_ to_ ~id i))
          ctx l
    | _ ->
        errorf_ "%a is not a (co)inductive constructor" ID.print_name id

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

  (* @return (v, ctx') where [ctx'] is a superset of [ctx] and [v] is a
     variable that does not occur in [ctx.vars]
     @param ty the type of the argument
     @param ctx the context, containing the current substitution, etc.
    *)
  let flatten_pat_
  : ctx:ctx -> ty:term -> term -> ctx * var
  = fun ~ctx ~ty t ->
    Utils.debugf ~section 3 "@[<2>flatten pattern `@[%a@]`@]" (fun k->k P.print t);
    match TMono.repr t with
    | TI.Var v ->
        if blocked_var_ ~ctx v
        then
          (* make a new var and ask for it to be equal to [v] *)
          let v' = Var.fresh_copy v in
          let ctx = add_constr_ ~ctx (EqTerm (U.var v, U.var v')) in
          ctx, v'
        else ctx, v (* use [v] directly as a pattern *)
    | TI.Const _
    | TI.App _
    | TI.Let _
    | TI.Match _
    | TI.Bind ((`Forall | `Exists | `Fun),_,_)
    | TI.AppBuiltin _ ->
        (* replace [t] with a fresh var [v] and add [v = t] as a guard
          to the RHS. *)
        let name = try ID.name (U.head_sym ty) with _ -> "v" in
        let v = Var.make ~ty ~name in
        (* add constraints for [v = t] *)
        let ctx = mk_eq ~ctx ~to_:(U.var v) t in
        ctx, v
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> errorf_ "expected pattern, got %a" P.print t

  let flatten_eqns ~defined ~env e =
    let Stmt.Eqn_nested l = e in
    let l = List.map
      (fun (_vars,args,rhs,side)  ->
        (* type of the defined term *)
        let ty_head = find_ty_ ~env defined.Stmt.defined_head in
        let ty_args = ty_args_ ty_head in
        Utils.debugf ~section 5 "type arguments: %a, term arguments: %a"
          (fun k->k(CCFormat.list P.print) ty_args (CCFormat.list P.print) args);
        assert (List.length ty_args = List.length args);
        (* map every argument to a variable, accumulating constraints and
           bindings along the way *)
        let ctx, vars = Utils.fold_map
          (fun ctx (arg,ty_arg) ->
            let ctx, v = flatten_pat_ ~ctx ~ty:ty_arg arg in
            (* forbid [v] from being used as a pattern in next arguments, for
              that would break linearity *)
            let ctx' = add_var_ ~ctx v in
            ctx', v
          ) (empty_ctx ~env) (List.combine args ty_args)
        in
        let rhs' = elim_match_ ~subst:ctx.subst rhs in
        let side = elim_match_l_ ~subst:ctx.subst side in
        (* add constraints to [side] *)
        let side' = List.map
          (fun constr -> match constr with
            | EqTerm (t1,t2) ->
                (* t1=t2 => rhs *)
                let t1 = elim_match_ ~subst:ctx.subst t1 in
                let t2 = elim_match_ ~subst:ctx.subst t2 in
                U.eq t1 t2
            | Test (t, id) ->
                let t = elim_match_ ~subst:ctx.subst t in
                mk_data_test_ ~id t
          ) ctx.c_set
        in
        vars, rhs', List.rev_append side' side
      ) l
    in
    Stmt.Eqn_linear l

  let elim_match_top_ t = elim_match_ ~subst:Subst.empty t
  let id_ x = x

  (* translate one single statement *)
  let tr_statement ~env st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        (* FIXME: declare the symbols of [l] before processing *)
        let env' = Env.declare_rec_funs ~env l in
        let l' = List.map
          (fun def ->
            let defined = def.Stmt.rec_defined in
            {def with
              Stmt.rec_eqns=flatten_eqns ~defined ~env:env' def.Stmt.rec_eqns;
            })
          l
        in
        let env = Env.rec_funs ~env l' in
        env, Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
        let l = Stmt.map_spec_defs ~term:elim_match_top_ ~ty:id_ l in
        let env = Env.spec_funs ~env l in
        env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) ->
        let l = List.map elim_match_top_ l in
        env, Stmt.axiom ~info l
    | Stmt.Decl (id,k,ty) ->
        let env = Env.declare ~kind:k ~env id ty in
        env, Stmt.mk_decl ~info id k ty
    | Stmt.TyDef (k,l) ->
        let env = Env.def_data ~env ~kind:k l in
        env, Stmt.mk_ty_def ~info k l
    | Stmt.Goal g ->
        let g = elim_match_top_ g in
        env, Stmt.goal ~info g

  let tr_problem pb =
    let env = Env.create() in
    let _, pb' = Problem.fold_map_statements
      ~x:env ~f:(fun env x -> tr_statement ~env x) pb
    in
    pb'

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
