
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

open Nunchaku_core

module A = UntypedAST
module E = CCResult
module ID = ID
module Var = Var
module MetaVar = MetaVar
module Loc = Location
module Stmt = Statement

module TI = TermInner
module TyI = TypePoly

type 'a or_error = ('a, string) CCResult.t
type id = ID.t
type 'a var = 'a Var.t
type loc = Loc.t

let fpf = Format.fprintf

let name = "ty_infer"
let section = Utils.Section.make name

type attempt_stack = UntypedAST.term list

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
        Some (Utils.err_sprintf "@[scoping for var %s:@ %s@ at %a@]"
          v msg Loc.print_opt loc)
    | IllFormed(what, msg, loc) ->
        Some (Utils.err_sprintf "@[<2>ill-formed %s:@ %s@ at %a@]"
          what msg Loc.print_opt loc)
    | TypeError (msg, stack) ->
        Some (Utils.err_sprintf "@[<2>type error:@ %s@ %a@]" msg print_stack stack)
    | _ -> None
  )

let scoping_error ?loc v msg = raise (ScopingError (v, msg, loc))

module MStr = Map.Make(String)

(* for the environment *)
type ('t, 'ty) term_def =
  | Decl of id * 'ty
  | TyVar of 'ty var
  | Var of 'ty var
  | Def of 't (* variable := this term *)

(** {2 Typed Term} *)
module Convert(Term : TermTyped.S) = struct
  module TyPoly = TypePoly.Make(Term)
  module U = TermTyped.Util(Term)
  module IU = TermInner.UtilRepr(Term)
  module Unif = TypeUnify.Make(Term)
  module VarSet = Var.Set(struct type t = Term.t end)

  type term = Term.t

  (* Helpers *)

  let push_ t stack = t::stack

  let type_error ~stack msg = raise (TypeError (msg, stack))
  let type_errorf ~stack fmt =
    Utils.exn_ksprintf fmt
      ~f:(fun msg -> TypeError(msg, stack))

  let ill_formed ?loc ?(kind="term") msg = raise (IllFormed (kind, msg, loc))
  let ill_formedf ?loc ?kind fmt =
    Utils.exn_ksprintf fmt
      ~f:(fun msg -> ill_formed ?loc ?kind msg)

  (* try to unify ty1 and ty2.
      @param stack the trace of inference attempts *)
  let unify_in_ctx_ ~stack ty1 ty2 =
    try
      Unif.unify_exn ty1 ty2
    with Unif.Fail _ as e ->
      type_error ~stack (Printexc.to_string e)

  (* polymorphic/parametrized type? *)
  let ty_is_poly_ t = match TyPoly.repr t with
    | TyI.Forall _ -> true
    | _ -> false

  module P = TI.Print(Term)

  (* Environment *)

  module TyEnv = struct
    type t = {
      vars: (term, term) term_def MStr.t; (* local vars *)
      cstors: (string, id * term) Hashtbl.t;  (* constructor ID + type *)
      datatypes: Term.t Stmt.ty_constructor ID.Map.t ID.Tbl.t;
        (* datatype -> ID + constructors *)
      attrs: Stmt.decl_attr list ID.Tbl.t;
      mutable metas: (string, term MetaVar.t) Hashtbl.t option;
    }
    (* map names to proper identifiers, with their definition *)

    let empty = {
      vars=MStr.empty;
      cstors=Hashtbl.create 16;
      datatypes=ID.Tbl.create 16;
      attrs=ID.Tbl.create 16;
      metas=None;
    }

    let remove ~env v = {env with vars=MStr.remove v env.vars; }

    let add_decl ~env v ~id ty = {
      env with vars=MStr.add v (Decl (id, ty)) env.vars;
    }

    let add_var ~env v ~var =
      let decl =
        if U.ty_returns_Type (Var.ty var)
        then TyVar var else Var var
      in
      { env with vars=MStr.add v decl env.vars }

    let add_vars ~env v l =
      assert (List.length v = List.length l);
      List.fold_left2
        (fun env v v' ->
          match v with
          | `Wildcard -> env
          | `Var v -> add_var ~env v ~var:v')
        env v l

    let add_def ~env v ~as_ = {
      env with vars=MStr.add v (Def as_) env.vars;
    }

    let mem_var ~env v = MStr.mem v env.vars

    let add_cstor ~env ~name c ty =
      if Hashtbl.mem env.cstors name
        then ill_formedf ~kind:"constructor"
          "a constructor named %s is already defined" name;
      Hashtbl.add env.cstors name (c,ty)

    let add_datatype ~env id cstors =
      if ID.Tbl.mem env.datatypes id
        then ill_formedf ~kind:"datatype" "%a already defined" ID.print id;
      ID.Tbl.add env.datatypes id cstors

    let find_var ?loc ~env v =
      try MStr.find v env.vars
      with Not_found -> scoping_error ?loc v "not bound in environment"

    let find_cstor ?loc ~env c =
      try Hashtbl.find env.cstors c
      with Not_found -> scoping_error ?loc c "not a known constructor"

    let find_datatype ?loc ~env c =
      try ID.Tbl.find env.datatypes c
      with Not_found ->
        scoping_error ?loc (ID.name c) "not a known (co)inductive type"

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

    let get_attrs ~env id = ID.Tbl.get_or ~or_:[] env.attrs id

    let set_attrs ~env id l =
      assert (not (ID.Tbl.mem env.attrs id));
      if l<>[] then ID.Tbl.add env.attrs id l

    (* reset table of meta-variables *)
    let reset_metas ~env = CCOpt.iter Hashtbl.clear env.metas
  end

  type env = TyEnv.t
  let empty_env = TyEnv.empty

  (* find the closest available location *)
  let rec get_loc_ ~stack t = match Loc.get_loc t, stack with
    | Some l, _ -> Some l
    | None, [] -> None
    | None, t' :: stack' -> get_loc_ ~stack:stack' t'

  let rec convert_ty_ ~stack ~env (ty:A.ty) =
    let loc = get_loc_ ~stack ty in
    let stack = push_ ty stack in
    match Loc.get ty with
      | A.Builtin `Prop -> U.ty_prop
      | A.Builtin `Type -> U.ty_type
      | A.Builtin `Unitype -> U.ty_unitype
      | A.Builtin s ->
          ill_formedf ?loc ~kind:"type" "%a is not a type" A.Builtin.print s
      | A.App (f, l) ->
          U.ty_app ?loc
            (convert_ty_ ~stack ~env f)
            (List.map (convert_ty_ ~stack ~env) l)
      | A.Var `Wildcard ->
          U.ty_meta_var ?loc (MetaVar.make ~name:"_")
      | A.Var (`Var v) ->
          begin match TyEnv.find_var ?loc ~env v with
            | Decl (id, t) ->
                (* var: _ ... _ -> Type mandatory *)
                unify_in_ctx_ ~stack (U.ty_returns t) U.ty_type;
                U.ty_const ?loc id
            | Var v -> ill_formedf ~kind:"type" "term variable %a in type" Var.print v
            | TyVar v ->
                unify_in_ctx_ ~stack
                  (U.ty_returns (Var.ty v))
                  U.ty_type;
                U.ty_var ?loc v
            | Def t -> t  (* expand def *)
          end
      | A.AtVar _ ->
          ill_formed ~kind:"type" ?loc "@ syntax is not available for types"
      | A.MetaVar v -> U.ty_meta_var (TyEnv.find_meta_var ~env v)
      | A.TyArrow (a,b) ->
          U.ty_arrow ?loc
            (convert_ty_ ~stack ~env a)
            (convert_ty_ ~stack ~env b)
      | A.TyForall (v,t) ->
          let var = Var.make ~ty:U.ty_type ~name:v in
          let env = TyEnv.add_var ~env v ~var in
          U.ty_forall ?loc var (convert_ty_ ~stack ~env t)
      | A.Asserting _ -> ill_formed ?loc "no `asserting` in types"
      | A.Mu _ -> ill_formed ?loc "no mu-binders in types"
      | A.Fun (_,_) -> ill_formed ?loc "no functions in types"
      | A.Let (_,_,_) -> ill_formed ?loc "no let in types"
      | A.Match _ -> ill_formed ?loc "no match in types"
      | A.Ite _ -> ill_formed ?loc "no if/then/else in types"
      | A.Forall (_,_)
      | A.Exists (_,_) -> ill_formed ?loc "no quantifiers in types"

  let convert_ty_exn ~env ty = convert_ty_ ~stack:[] ~env ty

  let convert_ty ~env ty =
    try E.return (convert_ty_exn ~env ty)
    with e -> E.of_exn e

  let prop = U.ty_prop
  let arrow_list ?loc = List.fold_right (U.ty_arrow ?loc)

  let fresh_ty_var_ ~name =
    let name = "ty_" ^ name in
    U.ty_meta_var (MetaVar.make ~name)

  (* number of "implicit" arguments (quantified) *)
  let rec num_implicit_ ty = match TyPoly.repr ty with
    | TyI.Forall (_,ty') -> 1 + num_implicit_ ty'
    | _ -> 0

  (* explore the type [ty], and add fresh type variables in the corresponding
     positions of [l] *)
  let rec fill_implicit_ ?loc ty l =
    match TyPoly.repr ty, l with
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
    include Var.Subst

    (* evaluate the type [ty] under the explicit substitution [subst] *)
    let rec eval ~subst ty =
      let loc = Term.loc ty in
      match TyPoly.repr ty with
      | TyI.Const _
      | TyI.Builtin _
      | TyI.Meta _ -> ty
      | TyI.Var v ->
          begin try
            let ty' = find_exn ~subst v in
            eval ~subst ty'
          with Not_found -> ty
          end
      | TyI.App (f,l) ->
          U.ty_app ?loc (eval ~subst f) (List.map (eval ~subst) l)
      | TyI.Arrow (a,b) ->
          U.ty_arrow ?loc (eval ~subst a) (eval ~subst b)
      | TyI.Forall (v,t) ->
          (* preserve freshness of variables *)
          let v' = Var.fresh_copy v in
          let subst = add ~subst v (U.ty_var v') in
          U.ty_forall ?loc v' (eval ~subst t)
  end

  let ty_apply t l =
    let apply_error t =
      type_errorf ~stack:[]
        "cannot apply type `@[%a@]` to anything" P.print t
    in
    let rec app_ ~subst t l = match TyPoly.repr t, l with
      | _, [] -> Subst.eval ~subst t
      | TyI.Builtin _, _
      | TyI.App (_,_),_
      | TyI.Const _, _ ->
          apply_error t
      | TyI.Var v, _ ->
          begin try
            let t = Subst.find_exn ~subst v in
            app_ ~subst t l
          with Not_found ->
            apply_error t
          end
      | TyI.Meta _,_ -> assert false
      | TyI.Arrow (a, t'), b :: l' ->
          unify_in_ctx_ ~stack:[] a b;
          app_ ~subst t' l'
      | TyI.Forall (v,t'), b :: l' ->
          let subst = Subst.add ~subst v b in
          app_ ~subst t' l'
    in
    app_ ~subst:Subst.empty t l

  let is_eq_ t = match Loc.get t with
    | A.Builtin (`Eq | `Equiv) -> true
    | _ -> false

  (* check that the map is exhaustive *)
  let check_cases_exhaustive_ ?loc ~env ~ty m =
    (* find the type definition *)
    let cstors = TyEnv.find_datatype ?loc ~env (U.head_sym ty) in
    let missing = ID.Map.fold
      (fun id _ acc ->
        if ID.Map.mem id m then acc else id::acc)
      cstors []
    in
    if missing=[] then `Ok else `Missing missing

  let check_prop_ ~stack t =
    unify_in_ctx_ ~stack (U.ty_exn t) U.ty_prop;
    t

  (* convert a parsed term into a typed/scoped term *)
  let rec convert_term_ ~stack ~env t =
    let loc = get_loc_ ~stack t in
    let stack = push_ t stack in
    match Loc.get t with
    | A.Builtin (`Eq | `Equiv) ->
        ill_formed ~kind:"term" ?loc "equality must be fully applied"
    | A.Builtin s ->
        (* only some symbols correspond to terms *)
        let b, ty = match s with
          | `Imply | `Or | `And | `Not -> ill_formed ?loc "partially applied connective"
          | `Prop -> ill_formed ?loc "`prop` is not a term, but a type"
          | `Type -> ill_formed ?loc "`type` is not a term"
          | `Unitype -> ill_formedf ?loc "`unitype` is not a term"
          | `True -> `True, prop
          | `False -> `False, prop
          | `Undefined _ | `Eq | `Equiv -> assert false (* dealt with earlier *)
        in
        U.builtin ?loc ~ty b
    | A.AtVar v ->
        begin match TyEnv.find_var ?loc ~env v with
          | Decl (id, ty) ->
              U.const ?loc ~ty id
          | TyVar v -> U.ty_var ?loc v
          | Var var -> U.var ?loc var
          | Def t -> t
        end
    | A.MetaVar v -> U.ty_meta_var (TyEnv.find_meta_var ~env v)
    | A.App (f, [a;b]) when is_eq_ f ->
        let a = convert_term_ ~stack ~env a in
        let b = convert_term_ ~stack ~env b in
        let ty = U.ty_exn a in
        unify_in_ctx_ ~stack ty (U.ty_exn b);
        U.eq ?loc a b
    | A.App (f, l) ->
        begin match Loc.get f, l with
        | A.Builtin `Imply, [a;b] ->
          let a = convert_term_ ~stack ~env a |> check_prop_ ~stack in
          let b = convert_term_ ~stack ~env b |> check_prop_ ~stack in
          U.builtin ~ty:prop (`Imply (a,b))
        | A.Builtin `Imply, _ -> ill_formed ?loc "wrong arity for `=>`"
        | A.Builtin `Or, _ ->
          let l = List.map (fun t -> convert_term_ ~stack ~env t |> check_prop_ ~stack) l in
          U.builtin ~ty:prop (`Or l)
        | A.Builtin `And, _ ->
          let l = List.map (fun t -> convert_term_ ~stack ~env t |> check_prop_ ~stack) l in
          U.builtin ~ty:prop (`And l)
        | A.Builtin `Not, [a] ->
          let a = convert_term_ ~stack ~env a |> check_prop_ ~stack in
          U.builtin ~ty:prop (`Not a)
        | A.Builtin `Not, _ -> ill_formed ?loc "wrong arity for `~`"
        | _ ->
          (* infer type of [f] *)
          let f' = convert_term_ ~stack ~env f in
          let ty_f = U.ty_exn f' in
          (* complete with implicit arguments, if needed *)
          let l = match Loc.get f with
            | A.AtVar _ -> l (* all arguments explicit *)
            | _ ->
                fill_implicit_ ?loc ty_f l
          in
          (* now, convert elements of [l] depending on what is
             expected by the type of [f] *)
          let ty, l' = convert_arguments_following_ty ty_f l
              ~stack ~env ~subst:Subst.empty in
          U.app ?loc ~ty f' l'
        end
    | A.Var (`Var v) ->
        (* a variable might be applied, too *)
        let head, ty_head = match TyEnv.find_var ?loc ~env v with
          | Decl (id, ty) ->
              U.const ?loc ~ty id, ty
          | Var var -> U.var ?loc var, Var.ty var
          | TyVar v -> U.ty_var ?loc v, Var.ty v
          | Def t -> t, U.ty_exn t
        in
        (* add potential implicit args *)
        let l = fill_implicit_ ?loc ty_head [] in
        (* convert [l] into proper types, of course *)
        let ty, l' = convert_arguments_following_ty
          ~stack ~env ~subst:Subst.empty ty_head l in
        U.app ?loc ~ty head l'
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
        let env = TyEnv.add_var ~env v ~var in
        let t = convert_term_ ~stack ~env t in
        (* NOTE: for dependent types, need to check whether [var] occurs in [type t]
           so that a forall is issued here instead of a mere arrow *)
        let ty = U.ty_arrow ?loc ty_var (U.ty_exn t) in
        U.fun_ ?loc var ~ty t
    | A.Mu ((v,ty_opt),t) ->
        let ty_var = fresh_ty_var_ ~name:v in
        (* unify with expected type *)
        CCOpt.iter
          (fun ty -> unify_in_ctx_ ~stack ty_var (convert_ty_exn ~env ty))
          ty_opt;
        let var = Var.make ~name:v ~ty:ty_var in
        let env = TyEnv.add_var ~env v ~var  in
        let t = convert_term_ ~stack ~env t in
        (* unify [ty t] with [ty_var], since [var = t] *)
        unify_in_ctx_ ~stack (U.ty_exn t) ty_var;
        U.mu ?loc var t
    | A.Let (v,t,u) ->
        let t = convert_term_ ~stack ~env t in
        let var = Var.make ~name:v ~ty:(U.ty_exn t) in
        let env = TyEnv.add_var ~env v ~var in
        let u = convert_term_ ~stack ~env u in
        U.let_ ?loc var t u
    | A.Match (t,l) ->
        let t = convert_term_ ~stack ~env t in
        let ty_t = U.ty_exn t in
        (* build map (cstor -> case) for pattern match *)
        let m = List.fold_left
          (fun m (c,vars,rhs) ->
            (* find the constructor and the (co)inductive type *)
            let c, ty_c = TyEnv.find_cstor ~env c in
            if ID.Map.mem c m
              then ill_formedf ?loc ~kind:"match"
                "constructor %a occurs twice in the list of cases"
                ID.print c;
            (* make scoped variables and infer their type from [t] *)
            let vars' = List.map
              (fun v ->
                let name = match v with `Wildcard -> "_" | `Var s -> s in
                Var.make ~name:"_" ~ty:(fresh_ty_var_ ~name))
              vars
            in
            let ty' = ty_apply ty_c (List.map Var.ty vars') in
            unify_in_ctx_ ~stack:[] ty_t ty';
            (* now infer the type of [rhs] *)
            let env = TyEnv.add_vars ~env vars vars' in
            let rhs = convert_term_ ~stack ~env rhs in
            ID.Map.add c (vars', rhs) m)
          ID.Map.empty l
        in
        (* force all right-hand sides to have the same type *)
        let ty = try
          let (id,(_,rhs)) = ID.Map.choose m in
          let ty = U.ty_exn rhs in
          ID.Map.iter
            (fun id' (_,rhs') ->
              if not (ID.equal id id')
                then unify_in_ctx_ ~stack:[] ty (U.ty_exn rhs'))
            m;
          ty
        with Not_found ->
          ill_formedf ?loc ~kind:"match" "pattern-match needs at least one case"
        in
        (* check the match is exhaustive and correct *)
        if not (TI.cases_well_formed m)
          then ill_formed ?loc ~kind:"match"
            "ill-formed pattern match (non linear pattern)";
        begin match check_cases_exhaustive_ ~env ~ty:ty_t m with
          | `Ok -> ()
          | `Missing l ->
              ill_formedf ?loc ~kind:"match"
                "pattern match is not exhaustive (missing %a)"
                (CCFormat.list ID.print) l
        end;
        (* ok, we're done here *)
        U.match_with ~ty t m
    | A.Ite (a,b,c) ->
        let a = convert_term_ ~stack ~env a in
        let b = convert_term_ ~stack ~env b in
        let c = convert_term_ ~stack ~env c in
        (* a:prop, and b and c must have the same type *)
        unify_in_ctx_ ~stack (U.ty_exn a) prop;
        unify_in_ctx_ ~stack (U.ty_exn b) (U.ty_exn c);
        U.ite ?loc a b c
    | A.Asserting (_, []) -> assert false
    | A.Asserting (t, l) ->
        let t = convert_term_ ~stack ~env t in
        let l = List.map (convert_term_ ~stack ~env) l in
        (* [l] is composed of propositions *)
        List.iter (fun p -> unify_in_ctx_ ~stack (U.ty_exn p) prop) l;
        U.asserting ?loc t l
    | A.Var `Wildcard ->
        (* TODO: generate fresh variable with new type?
            but then we need to quantify over it! *)
        type_error ~stack "term wildcards cannot be inferred"
    | A.TyForall _ -> type_error ~stack "terms cannot contain π"
    | A.TyArrow _ -> type_error ~stack "terms cannot contain arrows"

  (* convert elements of [l] into types or terms, depending on
     what [ty] expects. Return the converted list, along with
     what remains of [ty].
     @param subst the substitution of bound variables *)
  and convert_arguments_following_ty ~stack ~env ~subst ty l =
    match TyPoly.repr ty, l with
    | _, [] ->
        (* substitution is complete, evaluate [ty] now *)
        Subst.eval ~subst ty, []
    | TyI.Var _,_
    | TyI.App (_,_),_
    | TyI.Const _, _
    | TyI.Builtin _,_ ->
        type_errorf ~stack
          "@[<2>term of type @[%a@] cannot accept argument(s),@ \
            but was given [@[<hv>%a@]]@]"
          P.print ty (CCFormat.list ~start:"" ~stop:"" A.print_term) l
    | TyI.Meta var, b :: l' ->
        (* must be an arrow type. We do not infer forall types *)
        assert (MetaVar.can_bind var);
        (* convert [b] and [l'] *)
        let b = convert_term_ ~stack ~env b in
        let ty_b = U.ty_exn b in
        (* type of the function *)
        let ty_ret = U.ty_meta_var (MetaVar.make ~name:"_") in
        unify_in_ctx_ ~stack ty (U.ty_arrow ty_b ty_ret);
        (* application *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty_ret l' in
        ty', b :: l'
    | TyI.Arrow (a,ty'), b :: l' ->
        (* [b] must be a term whose type coincides with [subst a] *)
        let b = convert_term_ ~stack ~env b in
        let ty_b = U.ty_exn b in
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
    Utils.debugf ~section 3 "@[<2>new variable %a@ for %s@ within `@[%a@]`"
      (fun k-> k P.print ty_var v A.print_term t);
    (* unify with expected type *)
    CCOpt.iter
      (fun ty -> unify_in_ctx_ ~stack ty_var (convert_ty_exn ~env ty))
      ty_opt;
    let var = Var.make ~name:v ~ty:ty_var in
    let env = TyEnv.add_var ~env v ~var  in
    let t = convert_term_ ~stack ~env t in
    unify_in_ctx_ ~stack (U.ty_exn t) prop;
    (* which quantifier to build? *)
    let builder = match which with
      | `Forall -> U.forall
      | `Exists -> U.exists
    in
    builder ?loc var t

  let convert_term_exn ~env t = convert_term_ ~stack:[] ~env t

  let convert_term ~env t =
    try E.return (convert_term_exn ~env t)
    with e -> E.of_exn e

  type statement = (term, term) Stmt.t

  (* checks that the name is not declared/defined already *)
  let check_new_ ?loc ~env name =
    if TyEnv.mem_var ~env name
      then ill_formedf ~kind:"statement" ?loc
        "identifier %s already defined" name

  exception InvalidTerm of term * string
  (* term (or its type) is not valid, for given reason *)

  let () = Printexc.register_printer
    (function
      | InvalidTerm (t, msg) ->
          Some (Utils.err_sprintf "@[<2>invalid term `@[%a@]`:@ %s@]" P.print t msg)
      | _ -> None)

  let invalid_term_ t msg = raise (InvalidTerm (t,msg))

  (* check that [t] is a monomorphic type or a term in which types
    are prenex, without metas ; convert it into a [term2] *)
  let rec is_mono_ t =
    match Term.repr t with
    | TI.TyMeta _ -> invalid_term_ t "remaining meta-variable"
    | TI.TyBuiltin _
    | TI.Const _ ->  true
    | TI.Var v -> is_mono_var_ v
    | TI.App (f,l) -> is_mono_ f && List.for_all is_mono_ l
    | TI.Builtin b -> TI.Builtin.to_seq b |> Sequence.for_all is_mono_
    | TI.Let (v,t,u) ->
        is_mono_var_ v && is_mono_ t && is_mono_ u
    | TI.Match (t,l) ->
        is_mono_ t &&
        ID.Map.for_all
          (fun _ (vars,rhs) -> List.for_all is_mono_var_ vars && is_mono_ rhs)
          l
    | TI.Bind (`TyForall, _, _) -> false
    | TI.Bind (_,v,t) -> is_mono_var_ v && is_mono_ t
    | TI.TyArrow (a,b) -> is_mono_ a && is_mono_ b
  and is_mono_var_ v = is_mono_ (Var.ty v)

  (* check that [t] is a prenex type or a term in which types are monomorphic,
    and convert it to a [term2] *)
  and is_prenex_ t =
    match Term.repr t with
    | TI.TyBuiltin _
    | TI.Const _ -> true
    | TI.Var v -> is_mono_var_ v
    | TI.App (f,l) -> is_prenex_ f && List.for_all is_mono_ l
    | TI.Builtin b -> TI.Builtin.to_seq b |> Sequence.for_all is_mono_
    | TI.Bind (`TyForall, v, t) ->
        (* pi v:_. t is prenex if t is *)
        is_mono_var_ v && is_prenex_ t
    | TI.Bind (`Forall, v, t) when U.ty_returns_Type (Var.ty v) ->
        (* forall v:type. t is prenex if t is *)
        is_prenex_ t
    | TI.Bind (_,v,t) -> is_mono_var_ v && is_mono_ t
    | TI.Let _
    | TI.Match _
    | TI.TyArrow _ -> is_mono_ t
    | TI.TyMeta _ -> false

  let check_ty_is_prenex_ ?loc t =
    if not (is_prenex_ t)
    then ill_formedf ?loc "type `@[%a@]` is not prenex" P.print t

  (* does [t] contain only prenex types? If not, convert it into [term2] *)
  let check_prenex_types_ ?loc t =
    if not (is_prenex_ t)
    then ill_formedf ?loc
        "term `@[%a@]`@ contains non-prenex types" P.print t

  let check_ty_is_mono_ ?loc t =
    if not (is_mono_ t)
    then ill_formedf ?loc
        "type `@[%a@]`@ is not monomorphic" P.print t

  let check_mono_var_ v =
    if not (is_mono_var_ v)
    then ill_formedf "variable %a has a non-monomorphic type" Var.print v

  let generalize ~close t =
    Utils.debugf ~section 5 "@[<2>generalize@ `@[%a@]`,@ by %s@]"
      (fun k->k P.print t
      (match close with `Fun -> "fun" | `Forall -> "forall" | `NoClose -> "no_close"));
    (* type meta-variables *)
    let vars = U.free_meta_vars t |> ID.Map.to_list in
    let t, new_vars = List.fold_right
      (fun (_,var) (t,new_vars) ->
        (* transform the meta-variable into a regular (type) variable *)
        let var' = Var.make ~name:(MetaVar.id var |> ID.name) ~ty:U.ty_type in
        MetaVar.bind ~var (U.ty_var var');
        (* build a function over [var'] *)
        let t = match close with
          | `Fun ->
              (* fun v1, ... , vn => t
                of type
                forall v1, ..., vn => typeof t *)
              let ty_t = U.ty_exn t in
              U.fun_ ~ty:(U.ty_forall var' ty_t) var' t
          | `Forall -> U.forall var' t
          | `NoClose -> t
        in
        t, var' :: new_vars
      ) vars (t, [])
    in
    if new_vars <> [] then
      Utils.debugf ~section 3 "@[generalized `@[%a@]`@ w.r.t @[%a@]@]"
        (fun k-> k P.print t (CCFormat.list Var.print) new_vars);
    t, new_vars

  (* convert [t] into a prop, call [f], generalize [t] *)
  let convert_prop_ ?(before_generalize=CCFun.const ()) ~env t =
    let t = convert_term_exn ~env t in
    unify_in_ctx_ ~stack:[] (U.ty_exn t) prop;
    before_generalize t;
    let t, _ = generalize ~close:`Forall t in
    check_prenex_types_ t;
    t

  let free_ty_vars t =
    U.to_seq_free_vars t
    |> Sequence.filter
      (fun v -> U.ty_returns_Type (Var.ty v))

  (* checks that [t] only contains free variables from [vars].
    behavior depends on [rel]:
      {ul
        {- rel = `Equal means the set of free variables must be equal to [vars]}
        {- rel = `Subset means the set of free variables must be subset}
      }
  *)
  let check_vars ~vars ~rel t =
    let fvars = free_ty_vars t |> VarSet.of_seq in
    match rel with
      | `Equal ->
          if VarSet.equal fvars vars then `Ok
          else
            let symdiff =
              VarSet.(union (diff fvars vars) (diff vars fvars) |> to_list) in
            `Bad symdiff
      | `Subset ->
          if VarSet.subset fvars vars then `Ok
          else `Bad VarSet.(diff fvars vars |> to_list)

  (* check that no meta-variable remains in [t]
      @return [`Ok] in this case, [`Bad vars] otherwise *)
  let check_no_meta t =
    let metas = U.free_meta_vars t
      |> ID.Map.to_list
      |> List.map snd
    in
    if metas=[] then `Ok else `Bad metas

  (* does [t] contain the given [id]? *)
  let term_contains_ t ~id =
    U.to_seq t
      |> Sequence.exists
        (fun t -> match Term.repr t with
          | TI.Const id' when ID.equal id id' -> true
          | _ -> false)

  (* convert a specification *)
  let convert_spec_defs ?loc ~env (untyped_defined_l, ax_l) =
    (* what are we specifying? a list of [Stmt.defined] terms *)
    let defined_l, env', spec_vars = match untyped_defined_l with
      | [] -> assert false (* parser error *)
      | (v,ty) :: tail ->
          let id = ID.make v in
          let ty = convert_ty_exn ~env ty in
          (* generate fresh type variables *)
          let n = num_implicit_ ty in
          let vars = CCList.init n
            (fun i -> Var.make ~ty:U.ty_type ~name:(CCFormat.sprintf "a_%d" i)) in
          let t_vars = List.map (U.ty_var ?loc:None) vars in
          let defined = {Stmt.defined_head=id; defined_ty=ty;} in
          (* locally, ensure that [v] refers to the defined term *)
          let t = U.app ~ty:(ty_apply ty t_vars) (U.const ~ty id) t_vars in
          let env' = TyEnv.add_def ~env v ~as_:t in
          let env', l = Utils.fold_map
            (fun env' (v',ty') ->
              let id' = ID.make v' in
              let ty' = convert_ty_exn ~env ty' in
              let n' = num_implicit_ ty' in
              (* every specified symbol must have the same number of type args *)
              if n<>n'
                then ill_formedf ?loc ~kind:"spec"
                  "specified terms %s and %s respectively require %d and %d \
                   type arguments" v v' n n';
              let t' = U.app ~ty:(ty_apply ty' t_vars) (U.const id' ~ty:ty') t_vars in
              let env' = TyEnv.add_def ~env:env' v' ~as_:t' in
              env', {Stmt.defined_head=id'; defined_ty=ty';})
            env' tail
          in
          defined :: l, env', vars
    in
    (* convert axioms. Use [env'] so that the specified terms are actually
        expansed into their version applied to [spec_vars] *)
    let axioms = List.map
      (fun ax ->
        (* check that all the free type variables in [ax] are among [spec_vars] *)
        let before_generalize t =
          begin match check_no_meta t with
          | `Ok -> ()
          | `Bad vars' ->
            ill_formedf ?loc ~kind:"spec"
              "term `@[%a@]`@ contains non-generalized variables @[%a@]"
              P.print t (CCFormat.list MetaVar.print) vars'
          end;
          match check_vars ~vars:(VarSet.of_list spec_vars) ~rel:`Subset t with
          | `Ok -> ()
          | `Bad bad_vars ->
              ill_formedf ?loc ~kind:"spec"
                "axiom contains type variables @[`%a`@]@ \
                  that do not occur in defined term@ @[`%a`@]"
                (CCFormat.list Var.print) bad_vars P.print t
        in
        convert_prop_ ~before_generalize ~env:env' ax)
      ax_l
    in
    (* check that no meta remains *)
    List.iter check_mono_var_ spec_vars;
    let spec = {Stmt. spec_axioms=axioms; spec_vars; spec_defined=defined_l; } in
    let env = List.fold_left
      (fun env def ->
        let id = def.Stmt.defined_head in
        let ty = def.Stmt.defined_ty in
        TyEnv.add_decl ~env (ID.name id) ~id ty)
      env defined_l
    in
    env, spec

  (* change [fun x1...xn.t] into [[x1;...;xn], t] *)
  let rec extract_fun_ t = match Term.repr t with
    | TI.Bind (`Fun, v, t') ->
        let vars, rhs = extract_fun_ t' in
        v :: vars, rhs
    | _ -> [], t

  (* extract [forall vars. f args = rhs] from a prop *)
  let rec extract_eqn ~f t = match Term.repr t with
    | TI.Bind (`Forall, v, t') ->
        CCOpt.map
          (fun (vars,args,rhs) -> v::vars,args,rhs)
          (extract_eqn ~f t')
    | TI.Builtin (`Eq (l,r)) ->
        begin match Term.repr l with
        | TI.Const f' when ID.equal f f' ->
            let vars, rhs = extract_fun_ r in
            Some (vars, List.map (fun v -> U.var v) vars, rhs)
        | TI.App (f', args) ->
            begin match Term.repr f' with
            | TI.Const f' when ID.equal f f' ->
                let vars, rhs = extract_fun_ r in
                Some (vars, args @ List.map (fun v ->U.var v) vars, rhs)
            | _ -> None
            end
        | _ -> None
        end
    | TI.App (f', l) ->
        (* forall v1..vn. p *)
        begin match Term.repr f' with
          | TI.Const f' when ID.equal f f' ->
            Some ([], l, U.true_)
          | _ -> None
        end
    | _ -> None

  (* extract [forall vars. guard => f args] from a prop *)
  let rec extract_clause ~f t =
    match Term.repr t with
    | TI.Bind (`Forall, v, t') ->
        CCOpt.map
          (fun (vars, g, t) -> v::vars,g,t)
          (extract_clause ~f t')
    | TI.Builtin (`Imply (a,b)) ->
        begin try
          if ID.equal (U.head_sym b) f then Some ([], Some a, b) else None
        with Not_found -> None
        end
    | _ ->
        begin try
          if ID.equal (U.head_sym t) f then Some ([], None, t) else None
        with Not_found -> None
        end

  (* [f args = rhs], where [f : ty]. Maybe [f] is actually
    partially applied, in which case we create new variables [vars']
    and return them (along with the new atomic type) *)
  let complete_args_ args ty =
    let rec aux subst args ty = match args, Term.repr ty with
      | [], TI.Bind (`TyForall, v, ty') ->
          assert (IU.ty_returns_Type (Var.ty v));
          let v' = Var.make ~name:"v" ~ty:(Var.ty v) in
          let l, ty = aux (Subst.add ~subst v (U.var v')) [] ty' in
          v' :: l, ty
      | [], TI.TyArrow (ty_arg, ty') ->
          let v = Var.make ~name:"v" ~ty:ty_arg in
          let l, ty = aux subst [] ty' in
          v :: l, ty
      | a::args', TI.Bind (`TyForall, v', ty') ->
          aux (Subst.add ~subst v' a) args' ty'
      | _::args', TI.TyArrow (_, ty') -> aux subst args' ty'
      | _ -> [], Subst.eval ~subst ty
    in
    aux Subst.empty args ty

  (* check that [t], the converted version of [ax], contains only
     the type variables among [ty_vars]. [id] is the symbol being defined. *)
  let check_contains_only_ ?loc ~kind ~ty_vars id untyped_ax t =
    begin match check_no_meta t with
    | `Ok -> ()
    | `Bad vars' ->
      ill_formedf ?loc ~kind
        "@[<2>term `@[%a@]`@ contains non-generalized variables @[%a@]@]"
        P.print t (CCFormat.list MetaVar.print) vars'
    end;
    match check_vars ~vars:(VarSet.of_list ty_vars) ~rel:`Subset t with
    | `Ok -> ()
    | `Bad vars' ->
        ill_formedf ?loc ~kind:"rec def"
          "@[<2>equation `@[%a@]`,@ in definition of `@[%a@]`,@ \
            contains type variables `@[%a@]` that do not occur \
          in defined term@]"
          A.print_term untyped_ax ID.print id
          (CCFormat.list Var.print) vars'

  let prepare_defs ~env l =
    Utils.fold_map
      (fun env' (v,ty,l) ->
        (* convert the type *)
        let ty = convert_ty_exn ~env ty in
        let id = ID.make v in
        let v_as_t = U.const ~ty id in
        (* set of allowed type variables in the definitions of [v] *)
        let n  = num_implicit_ ty in
        let vars = CCList.init n
          (fun i -> Var.make ~ty:U.ty_type ~name:(CCFormat.sprintf "a_%d" i)) in
        Utils.debugf ~section 4 "@[<2>locally define %s as `@[%a@]`@]"
          (fun k -> k v P.print v_as_t);
        (* declare [v] in the scope of equations *)
        let env' = TyEnv.add_def ~env:env' v ~as_:v_as_t in
        env', (id,ty,vars,l))
      env l

  let convert_rec_defs ?loc ~env l =
    (* first, build new variables for the defined terms,
        and build [env'] in which the defined identifiers are bound to constants *)
    let env', l' = prepare_defs ~env l in
    (* convert the equations *)
    let l' = List.map
      (fun (id,ty,ty_vars,l) ->
        let defined = Stmt.mk_defined id ty in
        (* in the definitions of [id], actually ensure that [id.name]
           is bound to [id ty_vars]. This way we can be sure that all definitions
           will share the same set of type variables. *)
        let env'' = TyEnv.remove ~env:env' (ID.name id) in
        let env'' = TyEnv.add_def ~env:env'' (ID.name id)
          ~as_:(
            let ty_vars' = List.map (U.ty_var ?loc:None) ty_vars in
            U.app (U.const ~ty id) ty_vars' ~ty:(ty_apply ty ty_vars'))
        in
        let rec_eqns = List.map
          (fun untyped_ax ->
            (* sanity check: equation must not contain other type variables,
              and all type variables must be bound *)
            let before_generalize t =
              check_contains_only_ ?loc ~kind:"rec" ~ty_vars:ty_vars id untyped_ax t
            in
            let ax = convert_prop_ ~before_generalize ~env:env'' untyped_ax in
            (* decompose into a proper equation *)
            match extract_eqn ~f:id ax with
            | None ->
                ill_formedf ?loc
                  "@[<2>expected `@[forall <vars>.@ @[%a@] @[<hv><args>@ =@ <rhs>@]@]`@]"
                    ID.print id
            | Some (vars,args,rhs) ->
                List.iter (check_prenex_types_ ?loc) args;
                (* make sure that functions are totally applied *)
                let vars', ty' = complete_args_ args ty in
                let vars'_as_t = List.map (U.var ?loc:None) vars' in
                vars @ vars',
                args @ vars'_as_t,
                U.app ~ty:ty' rhs vars'_as_t,
                [])
          l
        in
        (* return case *)
        {Stmt.
          rec_defined=defined; rec_vars=ty_vars;
          rec_eqns=Stmt.Eqn_nested rec_eqns; })
      l'
    in
    env', l'

  (* graph from predicate to a list of, for each case,
       set of mutually recursive predicates it depends on *)
  type cases_graph_cell = {
    cgc_cases: ID.Set.t list;
      (* for each clause, the set of IDs that need be well founded for
         the clause to be a base case *)
    mutable cgc_has_base_case: bool option;
      (* does this predicate have a base case? None means "not computed" *)
  }

  type cases_graph = cases_graph_cell ID.Map.t

  (* given list of (co)predicates, compute it cases graph *)
  let compute_cg l : cases_graph =
    let mutual_ids =
      List.fold_left
        (fun acc p -> ID.Set.add (Stmt.defined_of_pred p |> Stmt.id_of_defined) acc)
        ID.Set.empty l
    in
    List.fold_left
      (fun cg p ->
         let id = Stmt.id_of_defined (Stmt.defined_of_pred p) in
         let cases =
           p.Stmt.pred_clauses
           |> List.map
             (fun c -> match c.Stmt.clause_guard with
                | None -> ID.Set.empty
                | Some t ->
                  U.to_seq_consts t
                |> Sequence.filter (fun id' -> ID.Set.mem id' mutual_ids)
                |> ID.Set.of_seq)
         in
         let c = {cgc_cases=cases; cgc_has_base_case=None} in
         ID.Map.add id c cg)
      ID.Map.empty l

  (* check that each element of [cg] has a base case, or depends on IDs that do *)
  let check_base_case ?loc cg =
    (* recursive traversal of graph *)
    let rec check id =
      let c = ID.Map.find id cg in
      match c.cgc_has_base_case with
        | Some res -> res
        | None ->
          (* avoid cycles *)
          c.cgc_has_base_case <- Some false;
          let res =
            List.exists (ID.Set.for_all check) c.cgc_cases
          in
          c.cgc_has_base_case <- Some res;
          res
    in
    let bad =
      ID.Map.keys cg
      |> Sequence.find (fun id -> if check id then None else Some id)
    in
    match bad with
      | None -> ()
      | Some id ->
        ill_formedf ?loc
          "@[<2>inductive predicate `%a` requires at least one base case@]" ID.print id

  let convert_preds ?loc ~env kind l =
    (* first, build new variables for the defined terms,
        and build [env'] in which the defined identifiers are bound to constants *)
    let env', l' = prepare_defs ~env l in
    (* convert the equations *)
    let l' = List.map
      (fun (id,ty,ty_vars,l) ->
        let defined = {Stmt.defined_head=id; defined_ty=ty; } in
        (* in the definitions of [id], actually ensure that [id.name]
           is bound to [id ty_vars]. This way we can be sure that all definitions
           will share the same set of type variables. *)
        let env'' = TyEnv.remove ~env:env' (ID.name id) in
        let env'' = TyEnv.add_def ~env:env'' (ID.name id)
          ~as_:(
            let ty_vars' = List.map (U.ty_var ?loc:None) ty_vars in
            U.app (U.const ~ty id) ty_vars' ~ty:(ty_apply ty ty_vars'))
        in
        let pred_clauses = List.map
        (* return case *)
          (fun untyped_ax ->
            (* sanity check: equation must not contain other type variables,
              and all type variables must be bound *)
            let before_generalize t =
              check_contains_only_ ?loc ~kind:"pred" ~ty_vars:ty_vars id untyped_ax t
            in
            let ax = convert_prop_ ~before_generalize ~env:env'' untyped_ax in
            (* decompose into a proper clause *)
            match extract_clause ~f:id ax with
            | None ->
                ill_formedf ?loc
                  "@[<2>expected `@[forall <vars>.@ <optional guard> => %a <args>@]`@]"
                    ID.print id
            | Some (vars,g,rhs) ->
                CCOpt.iter (check_prenex_types_ ?loc) g;
                {Stmt.
                  clause_concl=rhs; clause_guard=g; clause_vars=vars;
                }
          )
          l
        in
        {Stmt.
          pred_defined=defined; pred_tyvars=ty_vars;
          pred_clauses;
        })
      l'
    in
    (* basic check that predicate is well-founded *)
    if kind=`Pred then (
      let cg = compute_cg l' in
      check_base_case ?loc cg;
    );
    env', l'

  let ty_forall_l_ = List.fold_right (fun v t -> U.ty_forall v t)

  (* convert mutual (co)inductive types definition *)
  let convert_tydef ?loc ~env l =
    (* first, declare all the types *)
    let env, l = Utils.fold_map
      (fun env (name,vars,cstors) ->
        (* ensure this defines a type -> type -> ... -> type
          with as many arguments as [List.length vars] *)
        let ty = List.fold_right
          (fun _v t -> U.ty_arrow U.ty_type t)
          vars U.ty_type
        in
        let id = ID.make_full ~needs_at:false name in
        Utils.debugf ~section 3 "@[(co)inductive type %a: %a@]"
          (fun k-> k ID.print id P.print ty);
        (* declare *)
        let env' = TyEnv.add_decl ~env name ~id ty in
        env', (id,vars,ty,cstors))
      env l
    in
    (* then declare constructors. *)
    Utils.fold_map
      (fun env (id,vars,ty_id,cstors) ->
        (* Type variables are declared in each constructor's scope,
            but not in the scope of other types in the
            same recursive definition *)
        let env', vars' = Utils.fold_map
          (fun env v ->
            let var = Var.make ~name:v ~ty:U.ty_type in
            TyEnv.add_var ~env v ~var, var)
          env vars
        in
        let ty_being_declared =
          U.app ~ty:U.ty_type
            (U.const ~ty:ty_id id)
            (List.map (fun v->U.ty_var v) vars')
        in
        (* for each constructor, find its type and declare it *)
        let env, cstors = List.fold_left
          (fun (env,cstors) (name,ty_args) ->
            let ty_args = List.map (convert_ty_exn ~env:env') ty_args in
            let ty' = ty_forall_l_ vars' (arrow_list ty_args ty_being_declared) in
            let id' = ID.make_full ~needs_at:(vars<>[]) name in
            let env = TyEnv.add_decl ~env name ~id:id' ty' in
            Utils.debugf ~section 3 "@[constructor %a: %a@]"
              (fun k-> k ID.print id' P.print ty');
            TyEnv.add_cstor ~env ~name id' ty';
            (* newly built constructor *)
            check_ty_is_prenex_ ?loc ty';
            List.iter (check_ty_is_mono_ ?loc) ty_args;
            let c = {Stmt.
              cstor_name=id'; cstor_type=ty'; cstor_args=ty_args;
            } in
            env, ID.Map.add c.Stmt.cstor_name c cstors
          ) (env, ID.Map.empty) cstors
        in
        List.iter check_mono_var_ vars';
        (* remember the list of constructors for this type *)
        TyEnv.add_datatype ~env id cstors;
        check_ty_is_prenex_ ty_id;
        let tydef = {Stmt.
          ty_id=id; ty_vars=vars'; ty_type=ty_id; ty_cstors=cstors;
        } in
        env, tydef)
      env l

  let convert_copy ?loc ~env c =
    let name = c.A.id in
    let id = ID.make name in
    (* introduce type variables into env, locally *)
    let env', vars =
      Utils.fold_map
        (fun env v ->
          let v' = Var.make ~ty:U.ty_type ~name:v in
          let env = TyEnv.add_var ~env v ~var:v' in
          env, v')
        env c.A.copy_vars
    in
    let ty_id =
      arrow_list (List.map (fun _ -> U.ty_type) vars) U.ty_type in
    let ty_new =
      U.ty_app (U.const ~ty:ty_id id) (List.map (fun v->U.ty_var v) vars) in
    (* convert the type alias *)
    let ty_of = convert_ty_exn ~env:env' c.A.of_ in
    let ok_vars =
      check_vars ~rel:`Equal ty_of ~vars:(VarSet.of_list vars) in
    begin match ok_vars with
      | `Ok -> ()
      | `Bad subset ->
          ill_formedf ?loc ~kind:"copy"
            "@[<2>the type variables@ @[%a@]@ do not occur \
             in both the copy and the definition@]"
             (CCFormat.list Var.print_full) subset
    end;
    let abstract = ID.make_full ~needs_at:(vars<>[]) c.A.abstract in
    let ty_abstract = ty_forall_l_ vars (U.ty_arrow ty_of ty_new) in
    let concrete = ID.make_full ~needs_at:(vars<>[]) c.A.concrete in
    let ty_concrete = ty_forall_l_ vars (U.ty_arrow ty_new ty_of) in
    (* declare abstract and concrete *)
    let env = TyEnv.add_decl ~env name ~id ty_id in
    let env =
      TyEnv.add_decl ~env c.A.abstract ~id:abstract ty_abstract in
    let env =
      TyEnv.add_decl ~env c.A.concrete ~id:concrete ty_concrete in
    let c = Stmt.mk_copy
      ~of_:ty_of ~to_:ty_new ~vars ~ty:ty_id
      ~abstract:(abstract,ty_abstract)
      ~concrete:(concrete,ty_concrete) id in
    env, c

  module PStmt = Stmt.Print(P)(P)

  let convert_attr ~env a =
    let fail() = ill_formedf "ill-formed attribute %a" A.pp_attr a in
    match a with
    | ["max_card"; n] ->
        let n = try int_of_string n with _ -> fail() in
        Stmt.Attr_card_max n
    | ["min_card"; n] ->
        let n = try int_of_string n with _ -> fail() in
        Stmt.Attr_card_min n
    | ["infinite"] ->
        Stmt.Attr_infinite
    | ["approx_of"; id] ->
        begin match TyEnv.find_var ~env id with
          | Decl (id,_) -> Stmt.Attr_finite_approx id
          | _ -> ill_formedf "expected type identifier, got %s" id
        end
    | ["upcast"] -> Stmt.Attr_infinite_upcast
    | _ -> fail()

  let is_infinite_ ~env id =
    let l = TyEnv.get_attrs ~env id in
    List.exists (function Stmt.Attr_infinite -> true | _ -> false) l

  let is_approx_of_ ~env id ~of_ =
    let l = TyEnv.get_attrs ~env id in
    List.exists
      (function Stmt.Attr_finite_approx id' -> ID.equal id' of_ | _ -> false)
      l

  (* check that attributes are "sound" *)
  let check_attrs ?loc ~env id ty l =
    let min_card = ref 0 in
    let max_card = ref max_int in
    List.iter
      (function
        | Stmt.Attr_card_max n -> max_card := n
        | Stmt.Attr_card_min n -> min_card := n
        | Stmt.Attr_pseudo_prop
        | Stmt.Attr_pseudo_true
        | Stmt.Attr_card_hint _ -> assert false (* not in input *)
        | Stmt.Attr_incomplete
        | Stmt.Attr_abstract
        | Stmt.Attr_infinite
        | Stmt.Attr_exn _ -> ()
        | Stmt.Attr_finite_approx id' ->
          if not (is_infinite_ ~env id')
          then ill_formedf ?loc ~kind:"attributes"
              "`%a` cannot be a finite approximation of `%a`,@ \
               which is not infinite" ID.print id ID.print id'
        | Stmt.Attr_infinite_upcast ->
          let ok =
            match TyPoly.repr ty with
              | TyI.Arrow (a,b) ->
                begin match TyPoly.repr a, TyPoly.repr b with
                  | TyI.Const alpha, TyI.Const u ->
                    is_infinite_ ~env u && is_approx_of_ ~env alpha ~of_:u
                  | _ -> false
                end
              | _ -> false
          in
          if not ok
          then ill_formedf ?loc ~kind:"attributes"
              "expect type of `%a` to be `<finite approx> → <infinite type>`,@ \
               but got `@[%a@]`" ID.print id P.print ty;
      )
      l;
    if !min_card > !max_card
    then ill_formedf ?loc ~kind:"attributes"
     "cardinality bounds are unsat (min_card = %d, max_card = %d)" !min_card !max_card

  let convert_statement_exn ~env st =
    let name = st.A.stmt_name in
    let loc = st.A.stmt_loc in
    let info = {Stmt.name; loc; } in
    Utils.debugf ~section 2 "@[<hv2>infer types in@ `@[%a@]`@ at %a@]"
      (fun k-> k A.print_statement st Loc.print_opt loc);
    let st', env = match st.A.stmt_value with
    | A.Include _ ->
        ill_formed ?loc ~kind:"statement" "includes should have been eliminated"
    | A.Decl (v, ty, attrs) ->
        check_new_ ?loc ~env v;
        let ty = convert_ty_exn ~env ty in
        let id = ID.make_full ~needs_at:(ty_is_poly_ ty) v in
        let env = TyEnv.add_decl ~env v ~id ty in
        check_ty_is_prenex_ ?loc ty;
        (* parse attributes *)
        let attrs = List.map (convert_attr ~env) attrs in
        check_attrs ?loc ~env id ty attrs;
        TyEnv.set_attrs ~env id attrs;
        Stmt.decl ~info ~attrs id ty, env
    | A.Axiom l ->
        (* convert terms, and force them to be propositions *)
        let l = List.map (convert_prop_ ?before_generalize:None ~env) l in
        Stmt.axiom ~info l, env (* default *)
    | A.Spec s ->
        let env, s = convert_spec_defs ?loc ~env s in
        Stmt.axiom_spec ~info s, env
    | A.Rec s ->
        let env, s = convert_rec_defs ?loc ~env s in
        Stmt.axiom_rec ~info s, env
    | A.Def (a,b) ->
        (* simpler version of [A.Rec] *)
        let env, s = convert_rec_defs ?loc ~env
          [(a, A.wildcard ?loc (), [A.eq (A.var a) b])] in
        (* check that the definition is nonrecursive *)
        List.iter
          (fun def ->
            let id1 = def.Stmt.rec_defined.Stmt.defined_head in
            let l = match def.Stmt.rec_eqns with
              | Stmt.Eqn_nested l -> l
              | _ -> assert false
            in
            if List.exists
              (fun (_,_,rhs,_) -> term_contains_ ~id:id1 rhs)
              l
            then ill_formedf ?loc ~kind:"def"
              "right-hand side of definition contains defined symbol %a"
              ID.print id1)
          s;
        Stmt.axiom_rec ~info s, env
    | A.Data l ->
        let env, l = convert_tydef ?loc ~env l in
        Stmt.data ~info l, env
    | A.Codata l ->
        let env, l = convert_tydef ?loc ~env l in
        Stmt.codata ~info l, env
    | A.Pred (wf, l) ->
        let env, l = convert_preds ?loc ~env `Pred l in
        Stmt.pred ~info ~wf l, env
    | A.Copred (wf, l) ->
        let env, l = convert_preds ?loc ~env `Copred l in
        Stmt.copred ~info ~wf l, env
    | A.Copy c ->
        let env, c = convert_copy ?loc ~env c in
        Stmt.copy ~info c, env
    | A.Goal t ->
        (* same as axiom, convert to prop *)
        let t = convert_prop_ ~env t in
        Stmt.goal ~info t, env
    in
    Utils.debugf ~section 2 "@[<2>checked statement@ `@[%a@]`@]"
      (fun k-> k PStmt.print st');
    st', env

  let convert_statement ~env st =
    try E.return (convert_statement_exn ~env st)
    with e -> E.of_exn e

  type problem = (term, term) Problem.t

  let convert_problem_exn ~env l =
    let res = CCVector.create() in
    (* read statements *)
    let env = CCVector.fold
      (fun env st ->
        let st, env = convert_statement_exn ~env st in
        TyEnv.reset_metas ~env;
        CCVector.push res st;
        env)
      env l
    in
    let res = CCVector.freeze res in
    let pb =
      Problem.make res
        ~meta:Problem.Metadata.default
    in
    pb, env

  let convert_problem ~env st =
    try E.return (convert_problem_exn ~env st)
    with e -> E.of_exn e
end

module Make(T1 : TermTyped.S)(T2 : TermInner.S) = struct
  type term1 = T1.t
  type term2 = T2.t

  module HO2 = TermPoly.Make(T2)

  let pipe_with ~decode ~print =
    (* type inference *)
    let module Conv = Convert(T1) in
    let on_encoded =
      Utils.singleton_if print ()
        ~f:(fun () ->
          let module P = TI.Print(T1) in
          let module PPb = Problem.Print(P)(P) in
          Format.printf "@[<v2>@{<Yellow>after type inference@}: %a@]@." PPb.print)
    in
    Transform.make
      ~on_encoded
      ~name
      ~input_spec:Transform.Features.full
      ~encode:(fun l ->
        let problem, _ = l
          |> Conv.convert_problem_exn ~env:Conv.empty_env
        in
        problem, ())
      ~decode:(fun () x -> decode x)
      ()

  let pipe ~print =
    pipe_with ~decode:CCFun.id ~print
end
