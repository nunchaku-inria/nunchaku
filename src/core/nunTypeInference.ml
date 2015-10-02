
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

module A = NunUntypedAST
module E = CCError
module Sym = NunSymbol
module Var = NunVar
module Loc = NunLocation

module TyI = NunType_intf
module TI = NunTerm_intf

type 'a or_error = [`Ok of 'a | `Error of string]
type var = Var.t
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
module type TERM = sig
  include NunTerm_intf.S_WITH_UNIFIABLE_TY

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val builtin : ?loc:loc -> ty:Ty.t -> NunTerm_intf.Builtin.t -> t
  val var : ?loc:loc -> ty:Ty.t -> var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> var -> ty_arg:Ty.t -> t -> t
  val let_ : ?loc:loc -> var -> t -> t -> t
  val forall : ?loc:loc -> var -> ty_arg:Ty.t -> t -> t
  val exists : ?loc:loc -> var -> ty_arg:Ty.t -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunType_intf.Builtin.t -> Ty.t
  val ty_var : ?loc:loc -> var -> Ty.t
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

module ConvertTerm(Term : TERM) = struct
  module Unif = NunTypeUnify.Make(Term.Ty)

  (* Helpers *)

  type attempt_stack = NunUntypedAST.term list
  exception TypeError of string * attempt_stack

  (* print a stack *)
  let print_stack out st =
    let print_frame out t =
      fpf out "@[<hv 2>trying to infer type of %a at %a@]"
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
    | Some ty -> Unif.deref_rec ty

  let get_ty_ty_ (t:Term.Ty.t) = get_ty_ (t:>Term.t)

  (* Environment *)

  type term_def =
    | Def of Term.t
    | Decl of Term.Ty.t

  type env = (Var.t * term_def) MStr.t
  (* map names to proper identifiers, with their definition *)

  let empty_env = MStr.empty

  module ConvertTy = struct
    let rec convert_ ~stack ~(env:env) (ty:A.ty) =
      let loc = Loc.get_loc ty in
      let stack = push_ ty stack in
      match Loc.get ty with
        | A.Sym Sym.Prop -> Term.ty_prop
        | A.Sym Sym.Type -> Term.ty_type
        | A.Sym s -> ill_formedf ?loc ~kind:"type" "%a is not a type" Sym.print s
        | A.App (f, l) ->
            Term.ty_app ?loc
              (convert_ ~stack ~env f)
              (List.map (convert_ ~stack ~env) l)
        | A.Wildcard -> Term.ty_var ?loc (Var.make ~name:"_")
        | A.Var v ->
            begin try
              let var, def = MStr.find v env in
              let ok = match def with
                | Decl t -> Term.Ty.returns_Type t (* var: _ ... _ -> Type mandatory *)
                | Def t -> Term.Ty.returns_Type (get_ty_ t)
              in
              if not ok
                then type_errorf ~stack:(push_ ty stack)
                  "expected type, var %a is not a type" Var.print var;
              Term.ty_var ?loc var
            with Not_found -> scoping_error ?loc v "not bound in environment"
            end
        | A.AtVar _ -> ill_formed ?loc "@ syntax is not available for types"
        | A.TyArrow (a,b) ->
            Term.ty_arrow ?loc
              (convert_ ~stack ~env a)
              (convert_ ~stack ~env b)
        | A.TyForall (v,t) ->
            let var = Var.make ~name:v in
            let env = MStr.add v (var, Decl Term.ty_type) env in
            Term.ty_forall ?loc var (convert_ ~stack ~env t)
        | A.Fun (_,_) -> ill_formed ?loc "no functions in types"
        | A.Let (_,_,_) -> ill_formed ?loc "no let in types"
        | A.Forall (_,_)
        | A.Exists (_,_) -> ill_formed ?loc "no quantifiers in types"

    let convert_exn ~env ty = convert_ ~stack:[] ~env ty

    let convert ~env ty =
      try E.return (convert_exn ~env ty)
      with e -> E.of_exn e
  end

  let add_def ~env v ~var t = MStr.add v (var, Def t) env

  let add_decl ~env v ~var ty = MStr.add v (var, Decl ty) env

  let prop = Term.ty_prop
  let arrow_list ?loc = List.fold_right (Term.ty_arrow ?loc)

  let ty_of_def_ = function
    | Decl ty -> ty
    | Def t -> get_ty_ t

  let fresh_ty_var_ ~name =
    let name = "ty_" ^ name in
    Term.ty_var (Var.make ~name)

  (* find the variable and definition of [v] *)
  let find_ ?loc ~env v =
    try MStr.find v env
    with Not_found -> scoping_error ?loc v "unknown identifier"

  (* explore the type [ty], and add fresh type variables in the corresponding
     positions of [l] *)
  let rec fill_implicit_ ?loc ty l =
    let ty = Unif.deref_rec ty in
    match Term.Ty.view ty, l with
    | TyI.Forall (_,ty'), l ->
        (* implicit argument, insert a variable *)
        A.wildcard ?loc () :: fill_implicit_ ?loc ty' l
    | TyI.Kind, _
    | TyI.Type, _
    | TyI.Builtin _, _
    | TyI.Var _, _
    | TyI.App (_,_),_ -> l
    | TyI.Arrow _, [] -> [] (* need an explicit argument *)
    | TyI.Arrow (_,ty'), a :: l' ->
        (* explicit argument *)
        a :: fill_implicit_ ?loc ty' l'

  (* evaluate the type [ty] under the explicit substitution [subst] *)
  let rec eval_subst ~subst ty =
    let ty = Unif.deref_rec ty in
    let loc = Term.loc (Term.Ty.to_term ty) in
    match Term.Ty.view ty with
    | TyI.Kind
    | TyI.Type
    | TyI.Builtin _ -> ty
    | TyI.Var v ->
        begin try
          let ty' = Var.Map.find v subst in
          eval_subst ~subst ty'
        with Not_found -> ty
        end
    | TyI.App (f,l) ->
        Term.ty_app ?loc (eval_subst ~subst f) (List.map (eval_subst ~subst) l)
    | TyI.Arrow (a,b) ->
        Term.ty_arrow ?loc (eval_subst ~subst a) (eval_subst ~subst b)
    | TyI.Forall (v,t) ->
        (* preserve freshness of variables *)
        let v' = Var.fresh_copy v in
        let subst = Var.Map.add v (Term.ty_var v') subst in
        Term.ty_forall ?loc v' (eval_subst ~subst t)

  (* try to unify ty1 and ty2.
      @param stack the trace of inference attempts *)
  let unify_in_ctx_ ~stack ty1 ty2 =
    try
      Unif.unify_exn ty1 ty2
    with Unif.Fail _ as e ->
      type_error ~stack (Printexc.to_string e)

  (* convert a parsed term into a typed/scoped term *)
  let rec convert_ ~stack ~env t =
    let loc = Loc.get_loc t in
    let stack = push_ t stack in
    match Loc.get t with
    | A.Sym s ->
        (* only some symbols correspond to terms *)
        let module B = TI.Builtin in
        let prop1 = Term.ty_arrow prop prop in
        let prop2 = arrow_list [prop; prop] prop in
        let b, ty = match s with
          | Sym.Imply -> B.Imply, prop2
          | Sym.Equiv -> B.Equiv, prop2
          | Sym.Or -> B.Or, prop2
          | Sym.And -> B.And, prop2
          | Sym.Prop -> ill_formed ?loc "prop is not a term, but a type"
          | Sym.Type -> ill_formed ?loc "type is not a term"
          | Sym.Not -> B.Not, prop1
          | Sym.True -> B.True, prop
          | Sym.False -> B.False, prop
        in
        Term.builtin ?loc ~ty b
    | A.AtVar v ->
        let var, def = find_ ?loc ~env v in
        let ty = ty_of_def_ def in
        Term.var ?loc ~ty var
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
        let ty, l' = convert_following ~stack ~env ~subst:Var.Map.empty ty_f l in
        Term.app ?loc ~ty f' l'
    | A.Var v ->
        (* a variable might be applied, too *)
        let var, def = find_ ?loc ~env v in
        let ty_var = ty_of_def_ def in
        (* add potential implicit args *)
        let l = fill_implicit_ ?loc ty_var [] in
        (* convert [l] into proper types, of course *)
        let ty, l' = convert_following ~stack ~env ~subst:Var.Map.empty ty_var l in
        Term.app ?loc ~ty (Term.var ?loc ~ty:ty_var var) l'
    | A.Forall ((v,ty_opt),t) ->
        convert_quantifier ?loc ~stack ~env ~which:`Forall v ty_opt t
    | A.Exists ((v,ty_opt),t) ->
        convert_quantifier ?loc ~stack ~env ~which:`Exists v ty_opt t
    | A.Fun ((v,ty_opt),t) ->
        (* fresh variable *)
        let var = Var.make ~name:v in
        (* the type of [var] *)
        let ty_var = fresh_ty_var_ ~name:v in
        (* unify with expected type *)
        CCOpt.iter
          (fun ty ->
            unify_in_ctx_ ~stack ty_var (ConvertTy.convert_exn ~env ty)
          ) ty_opt;
        let env = add_decl ~env v ~var ty_var in
        let t = convert_ ~stack ~env t in
        (* NOTE: for dependent types, need to check whether [var] occurs in [type t]
           so that a forall is issued here instead of a mere arrow *)
        let ty = Term.ty_arrow ?loc ty_var (get_ty_ t) in
        Term.fun_ ?loc var ~ty ~ty_arg:(Unif.eval ty_var) t
    | A.Let (v,t,u) ->
        let var = Var.make ~name:v in
        let t = convert_ ~stack ~env t in
        let env = add_def ~env v ~var t in
        let u = convert_ ~stack ~env u in
        Term.let_ ?loc var t u
    | A.Wildcard -> type_error ~stack "term wildcards cannot be inferred"
    | A.TyForall _ -> type_error ~stack "terms cannot contain π"
    | A.TyArrow _ -> type_error ~stack "terms cannot contain arrows"

  (* convert elements of [l] into types or terms, depending on
     what [ty] expects. Return the converted list, along with
     what remains of [ty].
     @param subst the substitution of bound variables *)
  and convert_following ~stack ~env ~subst ty l =
    let ty = Unif.deref_rec ty in
    match Term.Ty.view ty, l with
    | _, [] ->
        (* substitution is complete, evaluate [ty] now *)
        eval_subst ~subst ty, []
    | TyI.Kind ,_
    | TyI.Type ,_
    | TyI.Var _,_
    | TyI.App (_,_),_
    | TyI.Builtin _,_ ->
        type_errorf ~stack "@[term of type %a cannot accept argument,@ but was given %a@]"
          Term.Ty.print ty (CCFormat.list A.print_term) l
    | TyI.Arrow (a,ty'), b :: l' ->
        (* [b] must be a term whose type coincides with [subst a] *)
        let b = convert_ ~stack ~env b in
        let ty_b = get_ty_ b in
        unify_in_ctx_ ~stack (eval_subst ~subst a) ty_b;
        (* continue *)
        let ty', l' = convert_following ~stack ~env ~subst ty' l' in
        ty', b :: l'
    | TyI.Forall (v,ty'), b :: l' ->
        (* [b] must be a type, and we replace [v] with [b] *)
        let b = ConvertTy.convert_exn ~env b in
        assert (Term.Ty.is_Type (get_ty_ty_ b));
        let subst = Var.Map.add v b subst in
        (* continue *)
        let ty', l' = convert_following ~stack ~env ~subst ty' l' in
        ty', (Term.Ty.to_term b) :: l'

  and convert_quantifier ?loc ~stack ~env ~which v ty_opt t =
    (* fresh variable *)
    let ty_var = fresh_ty_var_ ~name:v in
    (* unify with expected type *)
    CCOpt.iter
      (fun ty ->
        unify_in_ctx_ ~stack ty_var (ConvertTy.convert_exn ~env ty)
      ) ty_opt;
    let var = Var.make ~name:v in
    let env = add_decl ~env v ~var ty_var in
    let t = convert_ ~stack ~env t in
    (* which quantifier to build? *)
    let builder = match which with
      | `Forall -> Term.forall
      | `Exists -> Term.exists
    in
    builder ?loc var ~ty_arg:(Unif.eval ty_var) t

  let convert_exn ~env t = convert_ ~stack:[] ~env t

  let convert ~env t =
    try E.return (convert_exn ~env t)
    with e -> E.of_exn e

  let generalize t =
    let ty = get_ty_ t in
    let vars = Unif.free_vars ty |> Var.Set.elements in
    (* fun v1, ... , vn => t
      of type
      forall v1, ..., vn => typeof t *)
    let t = List.fold_right
      (fun v t ->
        let ty_t = get_ty_ t in
        Term.fun_ ~ty:(Term.ty_forall v ty_t) v ~ty_arg:Term.ty_type t
      ) vars t
    in
    t, vars
end

module type STATEMENT = sig
  include NunStatement_intf.S

  module T : TERM

  val loc : (_,_) t -> loc option

  val decl : ?loc:loc -> var -> T.Ty.t -> (_, T.Ty.t) t
  val def : ?loc:loc -> var -> T.t -> (T.t, _) t
  val axiom : ?loc:loc -> T.t -> (T.t,_) t
end

module ConvertStatement(St : STATEMENT) = struct
  module CT = ConvertTerm(St.T)
  module T = St.T
  module Ty = T.Ty

  type t = (T.t, Ty.t) St.t

  type env = CT.env

  let empty_env = CT.empty_env

  let convert_exn ~env st =
    let loc = Loc.get_loc st in
    match Loc.get st with
    | A.Decl (v, ty) ->
        let var = Var.make ~name:v in
        let ty = CT.ConvertTy.convert_exn ~env ty in
        let env = CT.add_decl ~env v ~var ty in
        St.decl ?loc var ty, env
    | A.Def ((v, ty_opt), t) ->
        let var = Var.make ~name:v in
        (* infer type for t *)
        let t = CT.convert_exn ~env t in
        (* generalize type and term *)
        let t, _ = CT.generalize t in
        let env = CT.add_def ~env v ~var t in
        (* unify with [ty_opt] if present *)
        CCOpt.iter
          (fun ty ->
            let ty = CT.ConvertTy.convert_exn ~env ty in
            CT.unify_in_ctx_ ~stack:[] ty (CT.get_ty_ t)
          ) ty_opt;
        St.def ?loc var t, env
    | A.Axiom t ->
        (* infer type for t *)
        let t = CT.convert_exn ~env t in
        (* be sure it's a proposition *)
        CT.Unif.unify_exn (CT.get_ty_ t) CT.prop;
        St.axiom ?loc t, env

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
