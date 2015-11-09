
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Flatten pattern-matching in Equations} *)

module ID = NunID
module Var = NunVar
module Stmt = NunStatement
module B = NunBuiltin
module TyI = NunType_intf
module TI = NunTerm_intf
module Subst = Var.Subst
module Env = NunEnv

type id = NunID.t
type inv = <poly:[`Mono]; meta:[`NoMeta]>

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some ("error in flatten_eqn: " ^ msg)
    | _ -> None
  )

let error_ msg = raise (Error msg)
let errorf_ fmt = NunUtils.exn_ksprintf fmt ~f:(fun msg -> error_ msg)
let section = NunUtils.Section.make "flatten_eqn"

module Make(T : NunTerm_ho.S) = struct
  module U = NunTerm_ho.Util(T)
  module SubstUtil = NunTerm_ho.SubstUtil(T)

  type term = inv T.t
  type var = term Var.t
  type env = (term, term, [`Linear]) NunEnv.t

  (* a constraint used to flatten pattern match *)
  type constraint_ =
    | EqTerm of term * term
    | Test of term * ID.t (* [t,cons] --> is_cons t *)

  let fpf = Format.fprintf
  let print_term = NunTerm_ho.print ~repr:T.repr

  let pp_constraint out = function
    | EqTerm (t1,t2) -> fpf out "@[<2>%a =@ %a@]" print_term t1 print_term t2
    | Test (t, id) -> fpf out "@[is-%a %a@]" ID.print_name id print_term t

  (* a local context for flattening patterns and equations *)
  type ctx = {
    env : (term, term, [`Linear]) Env.t;
    blocked_vars: var list; (* already introduced variables *)
    c_set: constraint_ list; (* constraints *)
    subst: (term, term) Subst.t (* substitution to apply to RHS *)
  }

  let empty_ctx ~env = { blocked_vars=[]; c_set=[]; subst=Subst.empty; env; }

  let add_constr_ ~ctx c =
    NunUtils.debugf ~section 4 "add constraint %a" (fun k-> k pp_constraint c);
    {ctx with c_set=c::ctx.c_set; }

  let add_subst_ ~ctx v t =
    NunUtils.debugf ~section 4 "add binding %a -> `%a`"
      (fun k-> k Var.print v print_term t);
    {ctx with subst=Subst.add ~subst:ctx.subst v t;}

  let add_var_ ~ctx v =
    NunUtils.debugf ~section 4 "block var %a" (fun k-> k Var.print v);
    {ctx with blocked_vars=v::ctx.blocked_vars; }

  let mk_data_select_ a ~id i = U.app_builtin (B.T.DataSelect (id,i)) [a]
  let mk_data_test_ a ~id = U.app_builtin (B.T.DataTest id) [a]

  let find_ty_ ~env id = match Env.find_ty ~env id with
    | Some t -> t
    | None -> errorf_ "could not find the type of %a" ID.print_name id

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match U.as_ty ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

  (* [v] already used in the pattern? *)
  let blocked_var_ ~ctx v = List.exists (Var.equal v) ctx.blocked_vars

  (* add enough constraints for making [t], a sub-pattern, equal to
     the term [to_].
     Returns a context updated with the necessary substitutions and constraints *)
  let rec mk_eq
  : ctx:ctx -> to_:term -> term -> ctx
  = fun ~ctx ~to_ t ->
    let t = SubstUtil.deref ~subst:ctx.subst t in
    match T.repr t with
    | TI.Var v ->
        assert (not (Subst.mem ~subst:ctx.subst v));
        if blocked_var_ ~ctx v
        then add_constr_ ~ctx (EqTerm (t, to_)) (* variable already bound *)
        else add_subst_ ~ctx v to_ (* TODO: occur check? *)
    | TI.Const id -> mk_eq_constr ~ctx ~to_ id []
    | TI.App (f, l) ->
        (* we only deal with [constructor l] *)
        begin match T.repr f with
        | TI.Const id -> mk_eq_constr ~ctx ~to_ id l
        | _ -> errorf_ "expected first-order pattern, got %a" print_term t
        end
    | TI.AppBuiltin (_,_)
    | TI.Let (_,_,_)
    | TI.Match (_,_) ->
        NunUtils.not_implemented "flatten equation: non inductive pattern"
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> errorf_ "expected pattern, got type %a" print_term t
    | TI.Bind (_,_,_) -> errorf_ "expected pattern, got %a" print_term t

  and mk_eq_constr
  : ctx:ctx -> to_:term -> id -> term list -> ctx
  = fun ~ctx ~to_ id l ->
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

  (* @return (v, ctx') where [ctx'] is a superset of [ctx] and [v] is a
     variable that does not occur in [ctx.vars]
     @param ty the type of the argument
     @param ctx the context, containing the current substitution, etc.
    *)
  let flatten_pat_
  : ctx:ctx -> ty:term -> term -> ctx * var
  = fun ~ctx ~ty t ->
    NunUtils.debugf ~section 3 "@[<2>flatten pattern `@[%a@]`@]" (fun k->k print_term t);
    match T.repr t with
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
    | TI.Bind ((TI.Forall | TI.Exists | TI.Fun),_,_)
    | TI.AppBuiltin _ ->
        (* replace [t] with a fresh var [v] and add [v = t] as a guard
          to the RHS. *)
        (* TODO: use [head ty] as a name? *)
        let v = Var.make ~ty ~name:"v" in
        (* add constraints for [v = t] *)
        let ctx = mk_eq ~ctx ~to_:(U.var v) t in
        ctx, v
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> errorf_ "expected pattern, got %a" print_term t


  let flatten_eqn ~defined ~env e =
    let Stmt.Eqn_nested (_vars,args,rhs,side) = e in
    (* type of the defined term *)
    let ty_head = find_ty_ ~env defined.Stmt.defined_head in
    let ty_args = ty_args_ ty_head in
    assert (List.length ty_args = List.length args);
    (* map every argument to a variable, accumulating constraints and
       bindings along the way *)
    let ctx, vars = NunUtils.fold_map
      (fun ctx (arg,ty_arg) ->
        let ctx, v = flatten_pat_ ~ctx ~ty:ty_arg arg in
        (* forbid [v] from being used as a pattern in next arguments, for
          that would break linearity *)
        let ctx' = add_var_ ~ctx v in
        ctx', v
      ) (empty_ctx ~env) (List.combine args ty_args)
    in
    let rhs' = SubstUtil.eval ~subst:ctx.subst rhs in
    let side = List.map (SubstUtil.eval ~subst:ctx.subst) side in
    (* add constraints to [side] *)
    let side' = List.map
      (fun constr -> match constr with
        | EqTerm (t1,t2) ->
            (* t1=t2 => rhs *)
            let t1 = SubstUtil.eval ~subst:ctx.subst t1 in
            let t2 = SubstUtil.eval ~subst:ctx.subst t2 in
            U.eq t1 t2
        | Test (t, id) ->
            let t = SubstUtil.eval ~subst:ctx.subst t in
            mk_data_test_ ~id t
      ) ctx.c_set
    in
    Stmt.Eqn_linear (vars, rhs', List.rev_append side' side)

  (* translate one single statement *)
  let tr_statement ~env st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        let l' = List.map
          (fun def ->
            let defined = def.Stmt.rec_defined in
            {def with
              Stmt.rec_eqns=List.map (flatten_eqn ~defined ~env) def.Stmt.rec_eqns
            })
          l
        in
        let env = Env.rec_funs ~env l' in
        env, Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
        let env = Env.spec_funs ~env l in
        env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) ->
        env, Stmt.axiom ~info l
    | Stmt.Decl (id,k,ty) ->
        let env = Env.declare ~kind:k ~env id ty in
        env, Stmt.mk_decl ~info id k ty
    | Stmt.TyDef (k,l) ->
        let env = Env.def_data ~env ~kind:k l in
        env, Stmt.mk_ty_def ~info k l
    | Stmt.Goal g -> env, Stmt.goal ~info g

  let tr_problem pb =
    let env = Env.create() in
    let _, pb' = NunProblem.fold_map_statements
      ~x:env ~f:(fun env x -> tr_statement ~env x) pb
    in
    pb'

  let pipe ~print =
    let open NunTransform in
    let on_encoded =
      if print then
        let module TH = NunTerm_ho in
        let funs = TH.mk_print ~repr:T.repr in
        [Format.printf "@[<v2>after flattening of equations: %a@]@."
          (NunProblem.print ~pty_in_app:funs.TH.print_in_app
            ~pt_in_app:funs.TH.print_in_app funs.TH.print funs.TH.print)]
      else [] in
    let encode pb = tr_problem pb, () in
    make1 ~name:"flatten_eqn"
      ~encode
      ~on_encoded
      ~decode:(fun () x -> x)
      ()
end
