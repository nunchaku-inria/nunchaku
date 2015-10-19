
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

module A = NunUntypedAST
module E = CCError
module ID = NunID
module Var = NunVar
module MetaVar = NunMetaVar
module Loc = NunLocation

module TyI = NunType_intf

type 'a or_error = [`Ok of 'a | `Error of string]
type id = NunID.t
type 'a var = 'a Var.t
type loc = Loc.t

let fpf = Format.fprintf
let spf = CCFormat.sprintf
let section = NunUtils.Section.make "type_infer"

type attempt_stack = NunUntypedAST.term list

exception ScopingError of string * string * loc option
exception IllFormed of string * string * loc option (* what, msg, loc *)
exception TypeError of string * attempt_stack

(* print a stack *)
let print_stack out st =
  let print_frame out t =
    fpf out "@[<hv 2>trying to infer type of@ `@[%a@]`@ at %a@]"
      A.print_term t Loc.print_opt (Loc.get_loc t) in
  fpf out "@[<hv>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_frame) st

let () = Printexc.register_printer
  (function
    | ScopingError (v, msg, loc) ->
        Some (spf "@[scoping error for var %s:@ %s@ at %a@]"
          v msg Loc.print_opt loc)
    | IllFormed(what, msg, loc) ->
        Some (spf "@[ill-formed %s:@ %s@ at %a@]"
          what msg Loc.print_opt loc)
    | TypeError (msg, stack) ->
        Some (spf "@[<2>type error:@ %s@ %a@]" msg print_stack stack)
    | _ -> None
  )

let scoping_error ?loc v msg = raise (ScopingError (v, msg, loc))

module MStr = Map.Make(String)

(** {2 Typed Term} *)
module type TERM = NunTerm_typed.S

module Convert(Term : TERM) = struct
  module Unif = NunTypeUnify.Make(Term.Ty)
  module PrintTerm = NunTerm_ho.Print(Term)

  (* Helpers *)

  let push_ t stack = t::stack

  let type_error ~stack msg = raise (TypeError (msg, stack))
  let type_errorf ~stack fmt =
    NunUtils.exn_ksprintf fmt
      ~f:(fun msg -> TypeError(msg, stack))

  let ill_formed ?loc ?(kind="term") msg = raise (IllFormed (kind, msg, loc))
  let ill_formedf ?loc ?kind fmt =
    NunUtils.exn_ksprintf fmt
      ~f:(fun msg -> ill_formed ?loc ?kind msg)

  (* obtain the type of a term *)
  let get_ty_ t = match Term.ty t with
    | None -> assert false
    | Some ty -> ty

  (* try to unify ty1 and ty2.
      @param stack the trace of inference attempts *)
  let unify_in_ctx_ ~stack ty1 ty2 =
    try
      Unif.unify_exn ty1 ty2
    with Unif.Fail _ as e ->
      type_error ~stack (Printexc.to_string e)

  (* polymorphic/parametrized type? *)
  let ty_is_poly_ t = match Term.Ty.view t with
    | TyI.Forall _ -> true
    | _ -> false

  (* Environment *)

  type term_def =
    | Decl of ID.t * Term.Ty.t
    | Var of Term.Ty.t var

  module Env = struct
    type t = {
      vars: term_def MStr.t;
      mutable metas: (string, Term.Ty.t MetaVar.t) Hashtbl.t option;
    }
    (* map names to proper identifiers, with their definition *)

    let empty = {
      vars=MStr.empty;
      metas=None;
    }

    let add_decl ~env v ~id ty = {
      env with vars=MStr.add v (Decl (id, ty)) env.vars
    }

    let add_var ~env v ~var = {
      env with vars=MStr.add v (Var var) env.vars
    }

    let mem_var ~env v = MStr.mem v env.vars

    let find_var ?loc ~env v =
      try MStr.find v env.vars
      with Not_found -> scoping_error ?loc v "not bound in environment"

    (* find a meta-var by its name, create it if non existent *)
    let find_meta_var ~env v =
      let tbl = match env.metas with
        | None ->
            let tbl = Hashtbl.create 16 in
            env.metas <- Some tbl;
            tbl
        | Some tbl -> tbl
      in
      try Hashtbl.find tbl v
      with Not_found ->
        let var = MetaVar.make ~name:v in
        Hashtbl.add tbl v var;
        var

    (* reset table of meta-variables *)
    let reset_metas ~env = CCOpt.iter Hashtbl.clear env.metas
  end

  type env = Env.t
  let empty_env = Env.empty

  let rec convert_ty_ ~stack ~env (ty:A.ty) =
    let loc = Loc.get_loc ty in
    let stack = push_ ty stack in
    match Loc.get ty with
      | A.Builtin A.Builtin.Prop -> Term.ty_prop
      | A.Builtin A.Builtin.Type -> Term.ty_type
      | A.Builtin s -> ill_formedf ?loc ~kind:"type" "%a is not a type" A.Builtin.print s
      | A.App (f, l) ->
          Term.ty_app ?loc
            (convert_ty_ ~stack ~env f)
            (List.map (convert_ty_ ~stack ~env) l)
      | A.Wildcard ->
          Term.ty_meta_var ?loc (MetaVar.make ~name:"_")
      | A.Var v ->
          begin match Env.find_var ?loc ~env v with
            | Decl (id, t) ->
                (* var: _ ... _ -> Type mandatory *)
                unify_in_ctx_ ~stack (Term.Ty.returns t) Term.ty_type;
                Term.ty_const ?loc id
            | Var v ->
                unify_in_ctx_ ~stack (Term.Ty.returns (Var.ty v)) Term.ty_type;
                Term.ty_var ?loc v
          end
      | A.AtVar _ ->
          ill_formed ~kind:"type" ?loc "@@ syntax is not available for types"
      | A.MetaVar v -> Term.ty_meta_var (Env.find_meta_var ~env v)
      | A.TyArrow (a,b) ->
          Term.ty_arrow ?loc
            (convert_ty_ ~stack ~env a)
            (convert_ty_ ~stack ~env b)
      | A.TyForall (v,t) ->
          let var = Var.make ~ty:Term.ty_type ~name:v in
          let env = Env.add_var ~env v ~var in
          Term.ty_forall ?loc var (convert_ty_ ~stack ~env t)
      | A.Fun (_,_) -> ill_formed ?loc "no functions in types"
      | A.Let (_,_,_) -> ill_formed ?loc "no let in types"
      | A.Ite _ -> ill_formed ?loc "no if/then/else in types"
      | A.Forall (_,_)
      | A.Exists (_,_) -> ill_formed ?loc "no quantifiers in types"

  let convert_ty_exn ~env ty = convert_ty_ ~stack:[] ~env ty

  let convert_ty ~env ty =
    try E.return (convert_ty_exn ~env ty)
    with e -> E.of_exn e

  let prop = Term.ty_prop
  let arrow_list ?loc = List.fold_right (Term.ty_arrow ?loc)

  let fresh_ty_var_ ~name =
    let name = "ty_" ^ name in
    Term.ty_meta_var (MetaVar.make ~name)

  (* explore the type [ty], and add fresh type variables in the corresponding
     positions of [l] *)
  let rec fill_implicit_ ?loc ty l =
    match Term.Ty.view ty, l with
    | TyI.Forall (_,ty'), l ->
        (* implicit argument, insert a variable *)
        A.wildcard ?loc () :: fill_implicit_ ?loc ty' l
    | TyI.Builtin _, _
    | TyI.Meta _, _
    | TyI.Const _, _
    | TyI.Var _, _
    | TyI.App (_,_),_ -> l
    | TyI.Arrow _, [] -> [] (* need an explicit argument *)
    | TyI.Arrow (_,ty'), a :: l' ->
        (* explicit argument *)
        a :: fill_implicit_ ?loc ty' l'

  module Subst = struct
    include Var.Subst(struct type t = Term.Ty.t end)

    (* evaluate the type [ty] under the explicit substitution [subst] *)
    let rec eval ~(subst:ty t) ty =
      let loc = Term.loc ty in
      match Term.Ty.view ty with
      | TyI.Const _
      | TyI.Builtin _ -> ty
      | TyI.Meta _ -> ty
      | TyI.Var v ->
          begin try
            let ty' = find_exn ~subst v in
            eval ~subst ty'
          with Not_found -> ty
          end
      | TyI.App (f,l) ->
          Term.ty_app ?loc (eval ~subst f) (List.map (eval ~subst) l)
      | TyI.Arrow (a,b) ->
          Term.ty_arrow ?loc (eval ~subst a) (eval ~subst b)
      | TyI.Forall (v,t) ->
          (* preserve freshness of variables *)
          let v' = Var.fresh_copy v in
          let subst = add ~subst v (Term.ty_var v') in
          Term.ty_forall ?loc v' (eval ~subst t)
  end

  let is_eq_ t = match Loc.get t with
    | A.Builtin A.Builtin.Eq -> true
    | _ -> false

  (* convert a parsed term into a typed/scoped term *)
  let rec convert_term_ ~stack ~env t =
    let loc = Loc.get_loc t in
    let stack = push_ t stack in
    match Loc.get t with
    | A.Builtin A.Builtin.Eq ->
        ill_formed ~kind:"term" ?loc "equality must be fully applied"
    | A.Builtin s ->
        (* only some symbols correspond to terms *)
        let module B = NunBuiltin.T in
        let prop1 = Term.ty_arrow prop prop in
        let prop2 = arrow_list [prop; prop] prop in
        let b, ty = match s with
          | A.Builtin.Imply -> B.Imply, prop2
          | A.Builtin.Or -> B.Or, prop2
          | A.Builtin.And -> B.And, prop2
          | A.Builtin.Prop -> ill_formed ?loc "`prop` is not a term, but a type"
          | A.Builtin.Type -> ill_formed ?loc "`type` is not a term"
          | A.Builtin.Not -> B.Not, prop1
          | A.Builtin.True -> B.True, prop
          | A.Builtin.False -> B.False, prop
          | A.Builtin.Eq -> assert false (* deal with earlier *)
        in
        Term.builtin ?loc ~ty b
    | A.AtVar v ->
        begin match Env.find_var ?loc ~env v with
          | Decl (id, ty) ->
              Term.const ?loc ~ty id
          | Var var -> Term.var ?loc var
        end
    | A.MetaVar v -> Term.ty_meta_var (Env.find_meta_var ~env v)
    | A.App (f, [a;b]) when is_eq_ f ->
        let a = convert_term_ ~stack ~env a in
        let b = convert_term_ ~stack ~env b in
        unify_in_ctx_ ~stack (get_ty_ a) (get_ty_ b);
        Term.eq ?loc a b
    | A.App (f, l) ->
        (* infer type of [f] *)
        let f' = convert_term_ ~stack ~env f in
        let ty_f = get_ty_ f' in
        (* complete with implicit arguments, if needed *)
        let l = match Loc.get f with
          | A.AtVar _ -> l (* all arguments explicit *)
          | _ -> fill_implicit_ ?loc ty_f l
        in
        (* now, convert elements of [l] depending on what is
           expected by the type of [f] *)
        let ty, l' = convert_arguments_following_ty
          ~stack ~env ~subst:Subst.empty ty_f l in
        Term.app ?loc ~ty f' l'
    | A.Var v ->
        (* a variable might be applied, too *)
        let head, ty_head = match Env.find_var ?loc ~env v with
          | Decl (id, ty) ->
              Term.const ?loc ~ty id, ty
          | Var var -> Term.var ?loc var, Var.ty var
        in
        (* add potential implicit args *)
        let l = fill_implicit_ ?loc ty_head [] in
        (* convert [l] into proper types, of course *)
        let ty, l' = convert_arguments_following_ty
          ~stack ~env ~subst:Subst.empty ty_head l in
        Term.app ?loc ~ty head l'
    | A.Forall ((v,ty_opt),t) ->
        convert_quantifier ?loc ~stack ~env ~which:`Forall v ty_opt t
    | A.Exists ((v,ty_opt),t) ->
        convert_quantifier ?loc ~stack ~env ~which:`Exists v ty_opt t
    | A.Fun ((v,ty_opt),t) ->
        (* fresh variable *)
        let ty_var = fresh_ty_var_ ~name:v in
        let var = Var.make ~ty:ty_var ~name:v in
        (* unify with expected type *)
        CCOpt.iter
          (fun ty ->
            unify_in_ctx_ ~stack ty_var (convert_ty_exn ~env ty)
          ) ty_opt;
        let env = Env.add_var ~env v ~var in
        let t = convert_term_ ~stack ~env t in
        (* NOTE: for dependent types, need to check whether [var] occurs in [type t]
           so that a forall is issued here instead of a mere arrow *)
        let ty = Term.ty_arrow ?loc ty_var (get_ty_ t) in
        Term.fun_ ?loc var ~ty t
    | A.Let (v,t,u) ->
        let t = convert_term_ ~stack ~env t in
        let var = Var.make ~name:v ~ty:(get_ty_ t) in
        let env = Env.add_var ~env v ~var in
        let u = convert_term_ ~stack ~env u in
        Term.let_ ?loc var t u
    | A.Ite (a,b,c) ->
        let a = convert_term_ ~stack ~env a in
        let b = convert_term_ ~stack ~env b in
        let c = convert_term_ ~stack ~env c in
        (* a:prop, and b and c must have the same type *)
        unify_in_ctx_ ~stack (get_ty_ a) Term.ty_prop;
        unify_in_ctx_ ~stack (get_ty_ b) (get_ty_ c);
        Term.ite ?loc a b c
    | A.Wildcard -> type_error ~stack "term wildcards cannot be inferred"
    | A.TyForall _ -> type_error ~stack "terms cannot contain π"
    | A.TyArrow _ -> type_error ~stack "terms cannot contain arrows"

  (* convert elements of [l] into types or terms, depending on
     what [ty] expects. Return the converted list, along with
     what remains of [ty].
     @param subst the substitution of bound variables *)
  and convert_arguments_following_ty ~stack ~env ~subst ty l =
    match Term.Ty.view ty, l with
    | _, [] ->
        (* substitution is complete, evaluate [ty] now *)
        Subst.eval ~subst ty, []
    | TyI.Var _,_
    | TyI.App (_,_),_
    | TyI.Const _, _
    | TyI.Builtin _,_ ->
        type_errorf ~stack
          "@[term of type @[%a@] cannot accept argument,@ but was given @[<hv>%a@]@]"
          Term.Ty.print ty (CCFormat.list A.print_term) l
    | TyI.Meta var, b :: l' ->
        (* must be an arrow type. We do not infer forall types *)
        assert (MetaVar.can_bind var);
        (* convert [b] and [l'] *)
        let b = convert_term_ ~stack ~env b in
        let ty_b = get_ty_ b in
        (* type of the function *)
        let ty_ret = Term.ty_meta_var (MetaVar.make ~name:"_") in
        MetaVar.bind ~var (Term.ty_arrow ty_b ty_ret);
        (* application *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty_ret l' in
        ty', b :: l'
    | TyI.Arrow (a,ty'), b :: l' ->
        (* [b] must be a term whose type coincides with [subst a] *)
        let b = convert_term_ ~stack ~env b in
        let ty_b = get_ty_ b in
        unify_in_ctx_ ~stack (Subst.eval ~subst a) ty_b;
        (* continue *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty' l' in
        ty', b :: l'
    | TyI.Forall (v,ty'), b :: l' ->
        (* [b] must be a type, and we replace [v] with [b] *)
        let b = convert_ty_exn ~env b in
        let subst = Subst.add ~subst v b in
        (* continue *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty' l' in
        ty', b :: l'

  and convert_quantifier ?loc ~stack ~env ~which v ty_opt t =
    (* fresh variable *)
    let ty_var = fresh_ty_var_ ~name:v in
    NunUtils.debugf ~section 3 "new variable %a for %s within %a"
      Term.Ty.print ty_var v A.print_term t;
    (* unify with expected type *)
    CCOpt.iter
      (fun ty ->
        unify_in_ctx_ ~stack ty_var (convert_ty_exn ~env ty)
      ) ty_opt;
    let var = Var.make ~name:v ~ty:ty_var in
    let env = Env.add_var ~env v ~var  in
    let t = convert_term_ ~stack ~env t in
    (* which quantifier to build? *)
    let builder = match which with
      | `Forall -> Term.forall
      | `Exists -> Term.exists
    in
    builder ?loc var t

  let convert_term_exn ~env t = convert_term_ ~stack:[] ~env t

  let convert_term ~env t =
    try E.return (convert_term_exn ~env t)
    with e -> E.of_exn e

  module U = NunTerm_intf.Util(Term)

  (* TODO ensure that no meta var remains *)
  let generalize ~close t =
    (* type meta-variables *)
    let vars = U.free_meta_vars t |> ID.Map.to_list in
    let t, new_vars = List.fold_right
      (fun (_,var) (t,new_vars) ->
        (* transform the meta-variable into a regular (type) variable *)
        let var' = Var.make ~name:(MetaVar.id var |> ID.name) ~ty:Term.ty_type in
        MetaVar.bind ~var (Term.ty_var var');
        (* build a function over [var'] *)
        let t = match close with
          | `Fun ->
              (* fun v1, ... , vn => t
                of type
                forall v1, ..., vn => typeof t *)
              let ty_t = get_ty_ t in
              Term.fun_ ~ty:(Term.ty_forall var' ty_t) var' t
          | `Forall -> Term.forall var' t
          | `NoClose -> t
        in
        t, var' :: new_vars
      ) vars (t, [])
    in
    if new_vars <> [] then
      NunUtils.debugf ~section 3 "@[generalized `%a`@ w.r.t @[%a@]@]"
        PrintTerm.print t (CCFormat.list Var.print) new_vars;
    t, new_vars

  module St = NunProblem.Statement

  type statement = (Term.t, Term.Ty.t) St.t

  (* checks that the name is not declared/defined already *)
  let check_new_ ?loc ~env name =
    if Env.mem_var ~env name
      then ill_formedf ~kind:"statement" ?loc
        "identifier %s already defined" name

  (* convert [t] into a prop, call [f], generalize [t] *)
  let convert_prop_ ?(before_generalize=CCFun.const ()) ~env t =
    let t = convert_term_exn ~env t in
    unify_in_ctx_ ~stack:[] (get_ty_ t) prop;
    before_generalize t;
    let t, _ = generalize ~close:`Forall t in
    t

  let convert_cases ?loc ~env l =
    let allowed_vars = ref [] in (* type variables that can occur in axioms *)
    List.map
      (fun (untyped_t,v,l) ->
        let t = convert_term_exn ~env untyped_t in
        (* replace meta-variables in [t] by real variables, and return those *)
        let t, vars = generalize ~close:`NoClose t in
        allowed_vars := vars @ !allowed_vars;
        (* declare [v] with the type of [t] *)
        let var, env' =
          let var = Var.make ~name:v ~ty:(get_ty_ t) in
          var, Env.add_var ~env v ~var
        in
        (* now convert axioms in the new env. They should contain no
          type variables but [vars]. *)
        let check_vars t =
          (* bad variables: occur freely in axiom but not in [vars] *)
          let bad_vars = U.to_seq_free_vars t
            |> Sequence.filter
              (fun v -> Term.Ty.returns_Type (Var.ty v))
            |> Sequence.filter
                (fun v -> not (CCList.Set.mem ~eq:Var.equal v !allowed_vars))
            |> Sequence.to_rev_list
            |> CCList.sort_uniq ~cmp:Var.compare
          in
          if bad_vars <> []
            then ill_formedf ?loc ~kind:"mutual def"
              "@[<2>axiom contains type variables @[`%a`@]@ \
              that do not occur in defined term@ @[`%a`@]@]"
              (CCFormat.list Var.print) bad_vars A.print_term untyped_t
        in
        let l = List.map
          (fun ax -> convert_prop_ ~before_generalize:check_vars ~env:env' ax)
          l
      in
        (* return case *)
        {St.case_alias=var; case_defined=t; case_axioms=l; case_vars=vars;}
      )
      l

  let rec fold_map_ f acc l = match l with
    | [] -> acc, []
    | x :: tail ->
        let acc, y = f acc x in
        let acc, tail' = fold_map_ f acc tail in
        acc, y :: tail'

  let ty_forall_l_ = List.fold_right (fun v t -> Term.ty_forall v t)

  (* convert type decl *)
  let convert_tydef ~env l =
    (* first, declare all the types *)
    let env, l = fold_map_
      (fun env (name,vars,cstors) ->
        (* ensure this defines a type -> type -> ... -> type
          with as many arguments as [List.length vars] *)
        let ty = List.fold_right
          (fun _v t -> Term.ty_arrow Term.ty_type t) vars Term.ty_type in
        let id = ID.make_full ~needs_at:false ~name in
        NunUtils.debugf ~section 3 "@[(co)inductive type %a: %a@]"
          ID.print_name id PrintTerm.print_ty ty;
        (* declare *)
        let env' = Env.add_decl ~env name ~id ty in
        env', (id,vars,ty,cstors)
      ) env l
    in
    (* then declare constructors. *)
    fold_map_
      (fun env (id,vars,ty_id,cstors) ->
        (* Type variables are declared in each constructor's scope,
            but not in the scope of other types in the
            same recursive definition *)
        let env', vars' = fold_map_
          (fun env v ->
            let var = Var.make ~name:v ~ty:Term.ty_type in
            Env.add_var ~env v ~var, var
          ) env vars
        in
        let ty_being_declared =
          Term.app ~ty:Term.ty_type
            (Term.const ~ty:ty_id id)
            (List.map (fun v->Term.var v) vars')
        in
        (* for each constructor, find its type and declare it *)
        let env, cstors = fold_map_
          (fun env (name,ty_args) ->
            let ty_args = List.map (convert_ty_exn ~env:env') ty_args in
            let ty' = ty_forall_l_ vars' (arrow_list ty_args ty_being_declared) in
            let id' = ID.make_full ~needs_at:(vars<>[]) ~name in
            let env = Env.add_decl ~env name ~id:id' ty' in
            NunUtils.debugf ~section 3 "@[constructor %a: %a@]"
              ID.print_name id' PrintTerm.print_ty ty';
            (* newly built constructor *)
            let c = {St.cstor_name=id'; cstor_type=ty'; cstor_args=ty_args; } in
            env, c
          ) env cstors
        in
        let tydef = {St.
          ty_id=id; ty_vars=vars'; ty_type=ty_id; ty_cstors=cstors
        } in
        env, tydef
      )
      env l

  let convert_statement_exn ~env st =
    let name = st.A.stmt_name in
    let loc = st.A.stmt_loc in
    let info = {St.name; loc; } in
    NunUtils.debugf ~section 2 "@[<hv2>infer types in@ %a@ at %a@]"
      A.print_statement st Loc.print_opt loc;
    let st', env = match st.A.stmt_value with
    | A.Decl (v, ty) ->
        check_new_ ?loc ~env v;
        let ty = convert_ty_exn ~env ty in
        let id = ID.make_full ~needs_at:(ty_is_poly_ ty) ~name:v in
        let env = Env.add_decl ~env v ~id ty in
        if Term.Ty.returns_Type ty
        then St.ty_decl ~info id ty, env (* id is a type *)
        else St.decl ~info id ty, env
    | A.Axiom l ->
        (* convert terms, and force them to be propositions *)
        let l = List.map (convert_prop_ ?before_generalize:None ~env) l in
        St.axiom ~info l, env
    | A.Spec s ->
        let s = convert_cases ?loc ~env s in
        St.axiom_spec ~info s, env
    | A.Rec s ->
        let s = convert_cases ?loc ~env s in
        St.axiom_rec ~info s, env
    | A.Data l ->
        let env, l = convert_tydef ~env l in
        St.data ~info l, env
    | A.Codata l ->
        let env, l = convert_tydef ~env l in
        St.codata ~info l, env
    | A.Goal t ->
        (* infer type for t *)
        let t = convert_term_exn ~env t in
        (* be sure it's a proposition
           XXX: for narrowing, could be of any type? *)
        unify_in_ctx_ ~stack:[] (get_ty_ t) prop;
        St.goal ~info t, env
    in
    NunUtils.debugf ~section 2 "@[<2>checked statement@ %a@]"
      (St.print PrintTerm.print PrintTerm.print_ty) st';
    st', env

  let convert_statement ~env st =
    try E.return (convert_statement_exn ~env st)
    with e -> E.of_exn e

  type problem = (Term.t, Term.Ty.t) NunProblem.t

  let convert_problem_exn ~env l =
    let rec aux acc ~env l = match l with
      | [] -> List.rev acc, env
      | st :: l' ->
          let st, env = convert_statement_exn ~env st in
          Env.reset_metas ~env;
          aux (st :: acc) ~env l'
    in
    let l, env = aux [] ~env l in
    NunProblem.make l, env

  let convert_problem ~env st =
    try E.return (convert_problem_exn ~env st)
    with e -> E.of_exn e
end

let pipe (type a) (type b) ~print
(module T1 : NunTerm_typed.S with type t = a)
(module T2 : NunTerm_ho.S with type t = b) =
  let module PrintT = NunTerm_ho.Print(T1) in
  (* we get back "regular" HO terms *)
  let module Erase = NunTerm_ho.Erase(T2) in
  (* type inference *)
  let module Conv = Convert(T1) in
  let print_problem = NunProblem.print PrintT.print T1.Ty.print in
  let on_encoded =
    if print
    then [Format.printf "@[<2>after type inference:@ %a@]@." print_problem]
    else []
  in
  NunTransform.make1
    ~on_encoded
    ~name:"type inference"
    ~encode:(fun l ->
      let problem = l
        |> Conv.convert_problem_exn ~env:Conv.empty_env
        |> fst
      in
      problem, ()
    )
    ~decode:(fun () (model : T2.t NunProblem.Model.t) ->
      let ctx = Erase.create () in
      NunProblem.Model.map model ~f:(Erase.erase ~ctx)
    ) ()
