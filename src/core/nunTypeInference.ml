
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

exception ScopingError of string * string * loc option
exception IllFormed of string * string * loc option (* what, msg, loc *)

let () = Printexc.register_printer
  (function
    | ScopingError (v, msg, loc) ->
        Some (spf "@[scoping error for var %s:@ %s@ at %a@]"
          v msg Loc.print_opt loc)
    | IllFormed(what, msg, loc) ->
        Some (spf "@[ill-formed %s:@ %s@ at %a@]"
          what msg Loc.print_opt loc)
    | _ -> None
  )

let scoping_error ?loc v msg = raise (ScopingError (v, msg, loc))

module MStr = Map.Make(String)

(** {2 Typed Term} *)
module type TERM = NunTerm_typed.S

module ConvertTerm(Term : TERM) = struct
  module Unif = NunTypeUnify.Make(Term.Ty)

  (* Helpers *)

  type attempt_stack = NunUntypedAST.term list
  exception TypeError of string * attempt_stack

  (* print a stack *)
  let print_stack out st =
    let print_frame out t =
      fpf out "@[<hv 2>trying to infer type of@ @[%a@] at@ %a@]"
        A.print_term t Loc.print_opt (Loc.get_loc t) in
    fpf out "@[<hv>%a@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_frame) st

  let () = Printexc.register_printer
    (function
      | TypeError (msg, stack) ->
          Some (spf "@[<2>type error:@ %s@ %a@]" msg print_stack stack)
      | _ -> None
    )

  let push_ t stack = t::stack

  let myksprintf ~f fmt =
    let buf = Buffer.create 32 in
    let out = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _ -> Format.pp_print_flush out (); raise (f (Buffer.contents buf)))
      out fmt

  let type_error ~stack msg = raise (TypeError (msg, stack))
  let type_errorf ~stack fmt =
    myksprintf fmt
      ~f:(fun msg -> TypeError(msg, stack))

  let ill_formed ?loc msg = raise (IllFormed ("term", msg, loc))
  let ill_formedf ?loc ?(kind="term") fmt =
    myksprintf fmt
      ~f:(fun msg -> IllFormed (kind, msg, loc))

  (* obtain the type of a term *)
  let get_ty_ t = match Term.ty t with
    | None -> assert false
    | Some ty -> ty

  (* Environment *)

  type term_def =
    | Def of ID.t * Term.t
    | Decl of ID.t * Term.Ty.t
    | Var of Term.Ty.t var

  type env = term_def MStr.t
  (* map names to proper identifiers, with their definition *)

  let empty_env = MStr.empty

  module ConvertTy = struct
    let rec convert_ ~stack ~(env:env) (ty:A.ty) =
      let loc = Loc.get_loc ty in
      let stack = push_ ty stack in
      match Loc.get ty with
        | A.Builtin A.Builtin.Prop -> Term.ty_prop
        | A.Builtin A.Builtin.Type -> Term.ty_type
        | A.Builtin s -> ill_formedf ?loc ~kind:"type" "%a is not a type" A.Builtin.print s
        | A.App (f, l) ->
            Term.ty_app ?loc
              (convert_ ~stack ~env f)
              (List.map (convert_ ~stack ~env) l)
        | A.Wildcard -> Term.ty_meta_var ?loc (MetaVar.make ~name:"?")
        | A.Var v ->
            begin try
              let def = MStr.find v env in
              match def with
                | Decl (id, t) ->
                    (* var: _ ... _ -> Type mandatory *)
                    if not (Term.Ty.returns_Type t)
                      then type_errorf ~stack:(push_ ty stack)
                        "@[<2>expected type,@ const %a is not a type@]" ID.print id;
                    Term.ty_const ?loc id
                | Def (id, t) ->
                    if not (Term.Ty.returns_Type (get_ty_ t))
                      then type_errorf ~stack:(push_ ty stack)
                        "@[<2>expected type,@ const %a is not a type@]" ID.print id;
                    Term.ty_const ?loc id
                | Var v ->
                    if not (Term.Ty.returns_Type (Var.ty v))
                      then type_errorf ~stack:(push_ ty stack)
                        "@[<2>expected type,@ var %a is not a type@]" Var.print v;
                    Term.ty_var ?loc v
            with Not_found -> scoping_error ?loc v "not bound in environment"
            end
        | A.AtVar _ -> ill_formed ?loc "@@ syntax is not available for types"
        | A.TyArrow (a,b) ->
            Term.ty_arrow ?loc
              (convert_ ~stack ~env a)
              (convert_ ~stack ~env b)
        | A.TyForall (v,t) ->
            let var = Var.make ~ty:Term.ty_type ~name:v in
            let env = MStr.add v (Var var) env in
            Term.ty_forall ?loc var (convert_ ~stack ~env t)
        | A.Fun (_,_) -> ill_formed ?loc "no functions in types"
        | A.Let (_,_,_) -> ill_formed ?loc "no let in types"
        | A.Ite _ -> ill_formed ?loc "no if/then/else in types"
        | A.Forall (_,_)
        | A.Exists (_,_) -> ill_formed ?loc "no quantifiers in types"

    let convert_exn ~env ty = convert_ ~stack:[] ~env ty

    let convert ~env ty =
      try E.return (convert_exn ~env ty)
      with e -> E.of_exn e
  end

  let add_def ~env v ~id t = MStr.add v (Def (id, t)) env

  let add_decl ~env v ~id ty = MStr.add v (Decl (id, ty)) env

  let add_var ~env v ~var = MStr.add v (Var var) env

  let prop = Term.ty_prop
  let arrow_list ?loc = List.fold_right (Term.ty_arrow ?loc)

  let ty_of_def_ = function
    | Decl (_,ty) -> ty
    | Def (_,t) -> get_ty_ t
    | Var v -> Var.ty v

  let fresh_ty_var_ ~name =
    let name = "ty_" ^ name in
    Term.ty_meta_var (MetaVar.make ~name)

  (* find the variable and definition of [v] *)
  let find_ ?loc ~env v =
    try MStr.find v env
    with Not_found -> scoping_error ?loc v "unknown identifier"

  (* explore the type [ty], and add fresh type variables in the corresponding
     positions of [l] *)
  let rec fill_implicit_ ?loc ty l =
    match Term.Ty.view ty, l with
    | TyI.Forall (_,ty'), l ->
        (* implicit argument, insert a variable *)
        A.wildcard ?loc () :: fill_implicit_ ?loc ty' l
    | TyI.Kind, _
    | TyI.Type, _
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
    module M = Map.Make(struct
      type t = Term.Ty.t Var.t
      let compare = Var.compare
    end)

    type t = Term.Ty.t M.t

    let empty = M.empty

    let bind ~subst v ty = M.add v ty subst

    (* evaluate the type [ty] under the explicit substitution [subst] *)
    let rec eval ~(subst:t) ty =
      let loc = Term.loc ty in
      match Term.Ty.view ty with
      | TyI.Kind
      | TyI.Type
      | TyI.Const _
      | TyI.Builtin _ -> ty
      | TyI.Meta _ -> ty
      | TyI.Var v ->
          begin try
            let ty' = M.find v subst in
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
          let subst = bind ~subst v (Term.ty_var v') in
          Term.ty_forall ?loc v' (eval ~subst t)
  end

  (* try to unify ty1 and ty2.
      @param stack the trace of inference attempts *)
  let unify_in_ctx_ ~stack ty1 ty2 =
    try
      Unif.unify_exn ty1 ty2
    with Unif.Fail _ as e ->
      type_error ~stack (Printexc.to_string e)

  let is_eq_ t = match Loc.get t with
    | A.Builtin A.Builtin.Eq -> true
    | _ -> false

  (* convert a parsed term into a typed/scoped term *)
  let rec convert_ ~stack ~env t =
    let loc = Loc.get_loc t in
    let stack = push_ t stack in
    match Loc.get t with
    | A.Builtin A.Builtin.Eq ->
        ill_formed ?loc "equality must be fully applied"
    | A.Builtin s ->
        (* only some symbols correspond to terms *)
        let module B = NunBuiltin.T in
        let prop1 = Term.ty_arrow prop prop in
        let prop2 = arrow_list [prop; prop] prop in
        let b, ty = match s with
          | A.Builtin.Imply -> B.Imply, prop2
          | A.Builtin.Equiv -> B.Equiv, prop2
          | A.Builtin.Or -> B.Or, prop2
          | A.Builtin.And -> B.And, prop2
          | A.Builtin.Prop -> ill_formed ?loc "prop is not a term, but a type"
          | A.Builtin.Type -> ill_formed ?loc "type is not a term"
          | A.Builtin.Not -> B.Not, prop1
          | A.Builtin.True -> B.True, prop
          | A.Builtin.False -> B.False, prop
          | A.Builtin.Eq -> assert false (* deal with earlier *)
        in
        Term.builtin ?loc ~ty b
    | A.AtVar v ->
        let def = find_ ?loc ~env v in
        begin match def with
          | Def (id, _)
          | Decl (id, _) ->
              let ty = ty_of_def_ def in
              Term.const ?loc ~ty id
          | Var var -> Term.var ?loc var
        end
    | A.App (f, [a;b]) when is_eq_ f ->
        let a = convert_ ~stack ~env a in
        let b = convert_ ~stack ~env b in
        unify_in_ctx_ ~stack (get_ty_ a) (get_ty_ b);
        Term.eq ?loc a b
    | A.App (f, l) ->
        (* infer type of [f] *)
        let f' = convert_ ~stack ~env f in
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
        let def = find_ ?loc ~env v in
        let head, ty_head = match def with
          | Def (id, _)
          | Decl (id, _) ->
              let ty = ty_of_def_ def in
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
            unify_in_ctx_ ~stack ty_var (ConvertTy.convert_exn ~env ty)
          ) ty_opt;
        let env = add_var ~env v ~var in
        let t = convert_ ~stack ~env t in
        (* NOTE: for dependent types, need to check whether [var] occurs in [type t]
           so that a forall is issued here instead of a mere arrow *)
        let ty = Term.ty_arrow ?loc ty_var (get_ty_ t) in
        Term.fun_ ?loc var ~ty t
    | A.Let (v,t,u) ->
        let t = convert_ ~stack ~env t in
        let var = Var.make ~name:v ~ty:(get_ty_ t) in
        let env = add_var ~env v ~var in
        let u = convert_ ~stack ~env u in
        Term.let_ ?loc var t u
    | A.Ite (a,b,c) ->
        let a = convert_ ~stack ~env a in
        let b = convert_ ~stack ~env b in
        let c = convert_ ~stack ~env c in
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
    | TyI.Kind ,_
    | TyI.Type ,_
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
        let b = convert_ ~stack ~env b in
        let ty_b = get_ty_ b in
        (* type of the function *)
        let ty_ret = fresh_ty_var_ ~name:"?" in
        MetaVar.bind ~var (Term.ty_arrow ty_b ty_ret);
        (* application *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty_ret l' in
        ty', b :: l'
    | TyI.Arrow (a,ty'), b :: l' ->
        (* [b] must be a term whose type coincides with [subst a] *)
        let b = convert_ ~stack ~env b in
        let ty_b = get_ty_ b in
        unify_in_ctx_ ~stack (Subst.eval ~subst a) ty_b;
        (* continue *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty' l' in
        ty', b :: l'
    | TyI.Forall (v,ty'), b :: l' ->
        (* [b] must be a type, and we replace [v] with [b] *)
        let b = ConvertTy.convert_exn ~env b in
        let subst = Subst.bind ~subst v b in
        (* continue *)
        let ty', l' = convert_arguments_following_ty ~stack ~env ~subst ty' l' in
        ty', b :: l'

  and convert_quantifier ?loc ~stack ~env ~which v ty_opt t =
    (* fresh variable *)
    let ty_var = fresh_ty_var_ ~name:v in
    (* unify with expected type *)
    CCOpt.iter
      (fun ty ->
        unify_in_ctx_ ~stack ty_var (ConvertTy.convert_exn ~env ty)
      ) ty_opt;
    let var = Var.make ~name:v ~ty:ty_var in
    let env = add_var ~env v ~var  in
    let t = convert_ ~stack ~env t in
    (* which quantifier to build? *)
    let builder = match which with
      | `Forall -> Term.forall
      | `Exists -> Term.exists
    in
    builder ?loc var t

  let convert_exn ~env t = convert_ ~stack:[] ~env t

  let convert ~env t =
    try E.return (convert_exn ~env t)
    with e -> E.of_exn e

  let generalize t =
    let ty = get_ty_ t in
    let vars = Unif.free_meta_vars ty |> ID.Map.to_list in
    (* fun v1, ... , vn => t
      of type
      forall v1, ..., vn => typeof t *)
    let t, new_vars = List.fold_right
      (fun (_,var) (t,new_vars) ->
        let ty_t = get_ty_ t in
        (* transform the meta-variable into a regular (type) variable *)
        let var' = Var.make ~name:(MetaVar.id var |> ID.name) ~ty:Term.ty_type in
        MetaVar.bind ~var (Term.ty_var var');
        (* build a function over [var'] *)
        Term.fun_ ~ty:(Term.ty_forall var' ty_t) var' t,
        var' :: new_vars
      ) vars (t, [])
    in
    t, new_vars
end

module ConvertStatement(T : TERM) = struct
  module St = NunProblem.Statement
  module CT = ConvertTerm(T)
  module T = T
  module Ty = T.Ty

  type t = (T.t, Ty.t) St.t

  type env = CT.env

  let empty_env = CT.empty_env

  let convert_exn ~(env:env) st =
    let loc = Loc.get_loc st in
    match Loc.get st with
    | A.Decl (v, ty) ->
        let id = ID.make ~name:v in
        let ty = CT.ConvertTy.convert_exn ~env ty in
        let env = CT.add_decl ~env v ~id ty in
        if Ty.returns_Type ty
        then St.ty_decl ?loc id ty, env (* id is a type *)
        else St.decl ?loc id ty, env
    | A.Def ((v, ty_opt), t) ->
        let id = ID.make ~name:v in
        (* infer type for t *)
        let t = CT.convert_exn ~env t in
        (* generalize type and term *)
        let t, _ = CT.generalize t in
        let env = CT.add_def ~env v ~id t in
        (* unify with [ty_opt] if present *)
        let ty = CT.get_ty_ t in
        CCOpt.iter
          (fun ty ->
            let ty = CT.ConvertTy.convert_exn ~env ty in
            CT.unify_in_ctx_ ~stack:[] ty (CT.get_ty_ t)
          ) ty_opt;
        begin match Ty.view ty with
        | TyI.Builtin NunBuiltin.Ty.Prop ->
            St.prop_def ?loc id t, env  (* prop def *)
        | _ ->
            St.def ?loc id ~ty t, env (* regular def *)
        end
    | A.Axiom t ->
        (* infer type for t *)
        let t = CT.convert_exn ~env t in
        (* be sure it's a proposition *)
        CT.Unif.unify_exn (CT.get_ty_ t) CT.prop;
        St.axiom ?loc t, env
    | A.Goal t ->
        (* infer type for t *)
        let t = CT.convert_exn ~env t in
        (* be sure it's a proposition
           XXX: for narrowing, could be of any type? *)
        CT.Unif.unify_exn (CT.get_ty_ t) CT.prop;
        St.goal ?loc t, env

  let convert ~env st =
    try E.return (convert_exn ~env st)
    with e -> E.of_exn e

  let convert_list_exn ~env l =
    let rec aux acc ~env l = match l with
      | [] -> List.rev acc, env
      | st :: l' ->
          let st, env = convert_exn ~env st in
          aux (st :: acc) ~env l'
    in
    aux [] ~env l

  let convert_list ~env st =
    try E.return (convert_list_exn ~env st)
    with e -> E.of_exn e
end
