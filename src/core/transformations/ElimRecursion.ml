
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = ID
module Var = Var
module TI = TermInner
module TyI = TypeMono
module Stmt = Statement
module Sig = Signature
module Pol = Polarity

type id = ID.t

let section = Utils.Section.make "recursion_elim"

type inv1 = <ty:[`Mono]; eqn:[`Single]; ind_preds:[`Absent]>
type inv2 = <ty:[`Mono]; eqn:[`Absent]; ind_preds:[`Absent]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)
  module Subst = Var.Subst
  module TyM = TypeMono.Make(T)

  type term = T.t
  type ty = T.t

  let fpf = Format.fprintf
  let spf = CCFormat.sprintf

  (* how to encode a single recursive function/predicate *)
  type fun_encoding = {
    fun_encoded_fun: id;
      (* name of function encoded this way *)
    fun_abstract_ty: ty;
      (* type of abstract values for the function *)
    fun_abstract_ty_id: id;
      (* symbol corresponding to [fun_abstract_ty] *)
    fun_concretization: (id * ty) list;
      (* for each parameter, concretization function *)
  }

  type decode_state = {
    approx_fun : fun_encoding ID.Tbl.t;
      (* concretization_fun -> function it is used to encode *)
    encoded_fun : fun_encoding ID.Tbl.t;
      (* recursive function -> its encoding *)
    abstract_ty : fun_encoding ID.Tbl.t;
      (* set of abstraction types *)
  }

  (** {6 Encoding} *)

  (* state used for the translation *)
  type state = {
    decode: decode_state;
      (* for decoding purpose *)
    mutable sigma: ty Sig.t;
      (* signature *)
  }

  let create_state() = {
    decode={
      approx_fun=ID.Tbl.create 16;
      encoded_fun=ID.Tbl.create 16;
      abstract_ty=ID.Tbl.create 16;
    };
    sigma=Sig.empty;
  }

  exception TranslationFailed of term * string
  (* not supposed to escape *)

  exception DecodingFailed of T.t option * string

  let fail_tr_ t msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

  let fail_decode_ ?term:t msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (DecodingFailed (t,msg)))

  let () = Printexc.register_printer
    (function
      | TranslationFailed (t,msg) ->
          Some (spf "@[<2>translation of `@[%a@]` failed:@ %s@]" P.print t msg)
      | DecodingFailed (None, msg) ->
          Some (spf "@[<2>decoding failed:@ %s@]" msg)
      | DecodingFailed (Some t, msg) ->
          Some (spf "@[<2>decoding of `@[%a@]` failed:@ %s@]" P.print t msg)
      | _ -> None)

  type local_state = {
    pol: Pol.t;
      (* local polarity *)
    subst: (term,term) Subst.t;
      (* local substitution *)
  }

  let empty_local_state = {pol=Pol.Pos; subst=Subst.empty; }

  let inv_pol ls = {ls with
    pol=Pol.inv ls.pol;
  }

  let no_pol ls = {ls with pol=Pol.NoPol}

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match TyM.repr ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

  (* combine side-conditions with [t], depending on polarity *)
  let add_conds pol t conds =
    if conds=[] then t, []
    else match pol with
    | Pol.Pos -> U.and_ [t; U.and_ conds], []
    | Pol.Neg -> U.or_ [t; U.not_ (U.and_ conds)], []
    | Pol.NoPol -> t, conds

  (*
    - apply substitution eagerly (build it when we enter `forall_f x. f x = t`)
    - when we meet `f t1...tn`:
        - add 1 constraint `exists alpha. And_i (proj_i alpha = t_i)`;
        - keep same term
  *)

  (* if [f] is a recursively defined function that is being eliminated,
      then return [Some def_of_f] *)
  let as_defined_ ~state f = match T.repr f with
    | TI.Const id ->
        begin try
          Some (id, ID.Tbl.find state.decode.encoded_fun id)
        with Not_found -> None
        end
    | _ -> None

  (* translate term/formula recursively. Returns new term and a list
    of side-conditions (guards) *)
  let rec tr_term_rec_ ~state ~local_state (t:term): term * term list =
    match T.repr t with
    | TI.Const _ -> t, []
    | TI.Var v ->
        (* substitute if needed; no side-condition *)
        let t' = match Subst.find ~subst:local_state.subst v with
          | None -> t
          | Some t' -> t'
        in t', []
    | TI.App (f,l) ->
        begin match as_defined_ ~state f, T.repr f, l with
          | Some (id, fundef), _, _ ->
              (* [f] is a recursive function we are encoding *)
              if List.length l <> List.length fundef.fun_concretization
                then fail_tr_ t
                  "defined function %a is partially applied (%d arguments, expected %d)"
                  ID.print id (List.length l) (List.length fundef.fun_concretization);
              (* existential variable *)
              let alpha = Var.make ~name:"a" ~ty:fundef.fun_abstract_ty in
              let conds = ref [] in
              let eqns = ref [] in
              let l' = List.map2
                (fun arg (proj,_ty_proj) ->
                  (* under a function: no polarity *)
                  let arg', cond_arg = tr_term_rec_ arg
                    ~state ~local_state:(no_pol local_state) in
                  let eqn = U.eq arg' (U.app (U.const proj) [U.var alpha]) in
                  eqns := eqn :: !eqns;
                  conds := cond_arg @ !conds;
                  arg'
                )
                l
                fundef.fun_concretization
              in
              conds := (U.exists alpha (U.and_ !eqns)) :: !conds;
              U.app f l', !conds
          | None, TI.Builtin `Not, [t] ->
              let t, cond = tr_term_rec_ ~state ~local_state:(inv_pol local_state) t in
              add_conds local_state.pol (U.not_ t) cond
          | None, TI.Builtin ((`Or | `And) as b), l ->
              let l_conds = List.map (tr_term_rec_ ~state ~local_state) l in
              let l, conds = List.split l_conds in
              add_conds local_state.pol (U.app_builtin b l) (List.flatten conds)
          | None, TI.Builtin `Imply, [a;b] ->
              let a, cond_a = tr_term_rec_ ~state ~local_state:(inv_pol local_state) a in
              let b, cond_b = tr_term_rec_ ~state ~local_state b in
              add_conds local_state.pol (U.imply a b) (List.append cond_a cond_b)
          | None, TI.Builtin ((`DataTest _ | `DataSelect _) as b), [t] ->
              let t', conds = tr_term_rec_ ~state ~local_state t in
              U.app_builtin b [t'], conds
          | None, _, _ ->
              (* combine side conditions from every sub-term *)
              let conds, l' = Utils.fold_map
                (fun conds t ->
                  let t', c = tr_term_rec_ t
                    ~state ~local_state:(no_pol local_state) in
                  List.rev_append c conds, t')
                [] l
              in
              U.app f l', conds
        end
    | TI.Builtin (`True | `False
        | `And | `Or | `Not | `Imply | `DataSelect _ | `DataTest _) ->
          t, [] (* partially applied, or constant *)
    | TI.Builtin (`Undefined _ as b) ->
        U.builtin (TI.Builtin.map b
          ~f:(fun t-> fst(tr_term_rec_ ~state ~local_state t))), []
    | TI.Builtin (`Equiv _) -> fail_tr_ t "cannot translate equivalence (polarity)"
    | TI.Builtin (`Eq (a,b)) ->
        let a, cond_a = tr_term_rec_ ~state ~local_state:(no_pol local_state) a in
        let b, cond_b = tr_term_rec_ ~state ~local_state:(no_pol local_state) b in
        add_conds local_state.pol
          (U.eq a b)
          (List.rev_append cond_a cond_b)
    | TI.Builtin (`Ite (a,b,c)) ->
        let a, cond_a = tr_term_rec_ ~state ~local_state:(no_pol local_state) a in
        let b, cond_b = tr_term_rec_ ~state ~local_state b in
        let c, cond_c = tr_term_rec_ ~state ~local_state c in
        let conds = (U.ite a (U.and_ cond_b) (U.and_ cond_c)) :: cond_a in
        add_conds local_state.pol (U.ite a b c) conds
    | TI.Bind (`Forall,v,t) ->
        let t', conds = tr_term_rec_ ~state ~local_state t in
        let cond = U.forall v (U.and_ conds) in
        U.forall v t', List.map (U.forall v) [cond]
    | TI.Bind (`Exists,v,t) ->
        let t, conds = tr_term_rec_ ~state ~local_state t in
        let cond = U.exists v (U.and_ conds) in
        add_conds local_state.pol (U.exists v t) [cond]
    | TI.Bind (`Fun,_,_) -> fail_tr_ t "translation of λ impossible"
    | TI.Let (v,t,u) ->
        (* rename [v] *)
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst:local_state.subst v (U.var v') in
        let t, c_t = tr_term_rec_ t ~state ~local_state:{subst; pol=Pol.NoPol;} in
        let u, c_u = tr_term_rec_ u ~state ~local_state:{local_state with subst;} in
        let conds = match c_u with
          | [] -> c_t
          | _::_ -> U.let_ v' t (U.and_ c_u) :: c_t
        in
        add_conds local_state.pol (U.let_ v' t u) conds
    | TI.Match (t, l) ->
        let t, ct = tr_term_rec_ ~state ~local_state t in
        let conds' = ref ID.Map.empty in
        let l = ID.Map.mapi
          (fun c (vars,rhs) ->
            let rhs, conds = tr_term_rec_ ~state ~local_state rhs in
            conds' := ID.Map.add c (vars, U.and_ conds) !conds';
            vars,rhs
          ) l
        in
        U.match_with t l, (U.match_with t !conds') :: ct
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, []
    | TI.Bind (`TyForall, _, _)
    | TI.TyMeta _ -> assert false

  let tr_term ~state ~local_state t =
    Utils.debugf ~section 4
      "@[<2>convert toplevel term@ `@[%a@]`@]" (fun k -> k P.print t);
    tr_term_rec_ ~state ~local_state t

  (* translate a top-level formula *)
  let tr_form ~state t =
    let t', conds = tr_term ~state ~local_state:empty_local_state t in
    if conds=[] then t'
    else U.imply (U.and_ conds) t'

  (* translate equation [eqn], which is defining the function
     corresponding to [fun_encoding].
     It returns an axiom instead. *)
  let tr_eqns ~state ~fun_encoding ty eqn =
    let Stmt.Eqn_single (vars,rhs) = eqn in
    (* quantify over abstract variable now *)
    let alpha = Var.make ~ty:fun_encoding.fun_abstract_ty ~name:"a" in
    (* replace each [x_i] by [proj_i var] *)
    assert (List.length vars = List.length fun_encoding.fun_concretization);
    let args' = List.map
      (fun (proj,_) -> U.app (U.const proj) [U.var alpha])
      fun_encoding.fun_concretization
    in
    let subst = Subst.add_list ~subst:Subst.empty vars args' in
    (* if defined ID is polarized, use its polarity *)
    let pol = ID.polarity fun_encoding.fun_encoded_fun in
    let local_state = { subst; pol; } in
    (* convert right-hand side and add its side conditions *)
    let lhs = U.app (U.const fun_encoding.fun_encoded_fun) args' in
    let rhs', conds = tr_term ~state ~local_state rhs in
    let mk_eq = if U.ty_returns_Prop ty then U.equiv else U.eq in
    U.forall alpha (U.and_ (mk_eq lhs rhs' :: conds))

  (* transform the recursive definition (mostly, its equations) *)
  let tr_rec_def ~state ~fun_encoding def =
    tr_eqns ~state ~fun_encoding def.Stmt.rec_defined.Stmt.defined_ty def.Stmt.rec_eqns

  let tr_rec_defs ~info ~state l =
    (* transform each axiom, considering case_head as rec. defined *)
    let new_stmts = ref [] in
    let add_stmt = CCList.Ref.push new_stmts in
    (* first, build and register an encoding for each defined function *)
    List.iter
      (fun def ->
        let id = def.Stmt.rec_defined.Stmt.defined_head in
        (* declare abstract type + projectors first *)
        let name = "G_" ^ ID.name id in
        let abs_type_id = ID.make name in
        let abs_type = U.ty_const abs_type_id in
        let ty = Sig.find_exn ~sigma:state.sigma id in
        (* projection function: one per argument. It has
          type  [abs_type -> type of arg] *)
        let projectors =
          List.mapi
            (fun i ty_arg ->
              let id' = ID.make (Printf.sprintf "proj_%s_%d" name i) in
              let ty' = U.ty_arrow abs_type ty_arg in
              id', ty'
            )
            (ty_args_ ty)
        in
        let fun_encoding = {
          fun_encoded_fun=id;
          fun_abstract_ty_id=abs_type_id;
          fun_abstract_ty=abs_type;
          fun_concretization=projectors;
        } in
        ID.Tbl.add state.decode.encoded_fun id fun_encoding;
        ID.Tbl.add state.decode.abstract_ty fun_encoding.fun_abstract_ty_id fun_encoding;
        (* declare abstract type + projectors + the function
           NOTE: we need to declare the function because it is no longer
            defined, only axiomatized *)
        add_stmt (Stmt.ty_decl ~info:Stmt.info_default abs_type_id U.ty_type);
        add_stmt (Stmt.decl ~info:Stmt.info_default
                  id def.Stmt.rec_defined.Stmt.defined_ty);
        List.iter
          (fun (proj,ty_proj) ->
            add_stmt (Stmt.decl ~info:Stmt.info_default proj ty_proj);
            ID.Tbl.add state.decode.approx_fun proj fun_encoding;
          )
          fun_encoding.fun_concretization;
      )
      l;
    (* then translate each definition *)
    let l' = List.map
      (fun def ->
        try
          let id = def.Stmt.rec_defined.Stmt.defined_head in
          let fun_encoding = ID.Tbl.find state.decode.encoded_fun id in
          tr_rec_def ~state ~fun_encoding def
        with TranslationFailed (t, msg) as e ->
          (* could not translate, keep old definition *)
          Utils.debugf ~section 1
            "@[<2>recursion elimination in@ @[%a@]@ \
              failed on subterm @[%a@]:@ %s@]"
              (fun k -> k PStmt.print (Stmt.axiom_rec ~info l) P.print t msg);
          raise e
      )
      l
    in
    (* add new statements (type declarations) before l' *)
    List.rev_append !new_stmts [Stmt.axiom ~info l']

  (* translate a statement *)
  let tr_statement ~state st =
    (* update signature *)
    state.sigma <- Sig.add_statement ~sigma:state.sigma st;
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Decl (id,k,l) -> [Stmt.mk_decl ~info id k l] (* no type declaration changes *)
    | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l] (* no (co) data changes *)
    | Stmt.Pred (wf, k, l) ->
        let l = Stmt.cast_preds l in
        [Stmt.mk_pred ~info ~wf k l]
    | Stmt.Axiom l ->
        begin match l with
        | Stmt.Axiom_rec l ->
            tr_rec_defs ~info ~state l
        | Stmt.Axiom_spec spec ->
            let spec' =
              Stmt.map_spec_defs ~term:(tr_form ~state) ~ty:CCFun.id spec
            in
            [Stmt.axiom_spec ~info spec']
        | Stmt.Axiom_std l ->
            let l = List.map
              (fun t -> tr_form ~state t)
              l in
            [Stmt.axiom ~info l]
        end
    | Stmt.Goal g ->
        [Stmt.goal ~info (tr_form ~state g)]

  let elim_recursion pb =
    let state = create_state() in
    let pb' = Problem.flat_map_statements ~f:(tr_statement ~state) pb in
    pb', state.decode

  (** {6 Decoding}

    We expect to get back a model where the encoded functions (and their
    projections) are decision trees over finite domains.

    To make things more readable for the user, we drop the projections
    from the model, and limit the encoded functions to the
    domain where their projections were defined (the domain on which it
    is not garbage) *)

  type finite_domain = {
    dom_fun: fun_encoding;
      (* function *)
    dom_dom: ID.t list;
      (* abstract domain *)
    dom_args: term list ID.Tbl.t;
      (* for each abstract value in the approximation type, the list of
         concrete arguments it  corresponds to *)
  }

  type finite_domains = finite_domain ID.Tbl.t
  (* map abstracted function -> its domain *)

  let pp_domain out d =
    let pp_tuple out (id,l) =
      fpf out "%a → (@[%a@])" ID.print id
        (CCFormat.list ~start:"" ~stop:"" P.print) l
    in
    fpf out "[@[<hv2>`%a`:@ %a@]]"
      ID.print d.dom_fun.fun_encoded_fun
      (CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_tuple) (ID.Tbl.to_seq d.dom_args)

  (* see whether [t] is of the form [var = const] *)
  let as_eqn_sym_ ~var:v t =
    match T.repr t with
    | TI.Builtin (`Eq (a,b)) ->
        begin match T.repr a, T.repr b with
        | TI.Var v', TI.Const c
        | TI.Const c, TI.Var v' ->
            if Var.equal v v' then Some c else None
        | _ -> None
        end
    | _ -> None

  (* see [t] as [fun args -> body] *)
  let rec as_fun_ t = match T.repr t with
    | TI.Bind (`Fun, v, t') ->
        let args, body = as_fun_ t' in
        v :: args, body
    | _ -> [], t

  type proj_decision_tree =
    | Proj_E of T.t (* last case *)
    | Proj_If of ID.t * T.t * proj_decision_tree (* if x=id then term else tree *)

  type proj_fun = {
    proj_var: T.t Var.t;  (* argument to the projection function *)
    proj_tree: proj_decision_tree;
  }

  let rec extract_proj_tree_ v t = match T.repr t with
    | TI.Builtin (`Ite (a,b,c)) ->
        begin match as_eqn_sym_ ~var:v a with
          | Some id -> Proj_If (id, b, extract_proj_tree_ v c)
          | None -> Proj_E t
        end
    | _ -> Proj_E t

  let extract_proj_ t = match T.repr t with
    | TI.Bind (`Fun, v, body) ->
        { proj_var=v; proj_tree=extract_proj_tree_ v body; }
    | _ -> fail_decode_ ~term:t "expected a function"

  (*
     - gather definitions of projections
     - gather domains of abstract types
  *)
  let pass1_ ~state m =
    let projs = ID.Tbl.create 16 in
    let doms = ID.Tbl.create 16 in
    Model.iter m
      ~terms:(fun (t,u) -> match T.repr t with
        | TI.Const id ->
            if ID.Tbl.mem state.approx_fun id
            then ID.Tbl.add projs id (extract_proj_ u)
        | _ -> ())
      ~finite_types:(fun (ty,dom) -> match T.repr ty with
        | TI.Const id ->
            begin try
              let dom_fun = ID.Tbl.find state.abstract_ty id in
              let dom_dom = List.map
                (fun t -> match T.repr t with
                  | TI.Const id' -> id'
                  | _ ->
                    fail_decode_ ~term:t
                      "expected finite domains elements to be constants, got `@[%a@]`"
                      P.print t)
                dom
              in
              let dom = {dom_fun; dom_dom; dom_args=ID.Tbl.create 16; } in
              ID.Tbl.add doms dom_fun.fun_encoded_fun dom
            with Not_found -> ()
            end
        | _ -> ());
      projs, doms

  (* compute map `abstract type -> set of tuples by projection` *)
  let pass2_ projs (doms:finite_domains) =
    (* evaluate projection function on [id] *)
    let rec eval_proj_ dt id = match dt with
      | Proj_E t -> t
      | Proj_If (id', a, dt') ->
          if ID.equal id id' then a else eval_proj_ dt' id
    in
    ID.Tbl.iter
      (fun _ fdom ->
        List.iter
          (fun val_id ->
            let args = List.map
              (fun (f_id,_) ->
                let proj =
                  try ID.Tbl.find projs f_id
                  with Not_found ->
                    fail_decode_ "could not find value of projection function %a on %a"
                      ID.print f_id ID.print val_id
                in
                eval_proj_ proj.proj_tree val_id)
              fdom.dom_fun.fun_concretization
            in
            ID.Tbl.add fdom.dom_args val_id args)
          fdom.dom_dom
      )
      doms;
    ()

  (* translate definitions of rec. functions based on
      the map (only keep in the domain, tuples that are obtained by
      projections, the rest is junk)
  *)
  let pass3_ ~state doms m =
    let is_and_ t = match T.repr t with TI.Builtin `And -> true | _ -> false in
    (* evaluate a boolean condition *)
    let rec eval_cond_ ~subst t =
      let t = U.deref ~subst t in
      match T.repr t with
      | TI.App(b, l) when is_and_ b -> List.for_all (eval_cond_ ~subst) l
      | TI.Builtin (`Eq (a,b)) -> U.equal_with ~subst a b
      | _ -> fail_decode_ ~term:t "expected a boolean condition"
    in
    (* evaluate the body of a function with the given substitution *)
    let rec eval_body subst t =
      let t = U.deref ~subst t in
      match T.repr t with
      | TI.Builtin (`Ite (a,b,c)) ->
          if eval_cond_ ~subst a then b
          else eval_body subst c
      | TI.Let (v, t, u) ->
          let subst = Subst.add ~subst v (U.eval ~subst t) in
          eval_body subst u
      | _ -> U.eval ~subst t  (* yield *)
    in
    (* decode a function *)
    let decode_fun_ f_id dom t =
      let arity = List.length dom.dom_fun.fun_concretization in
      let args, body = as_fun_ t in
      if List.length args <> arity
        then fail_decode_ ~term:t "expected a function of %d arguments" arity;
      (* compute value of the function applied to [tup] *)
      let apply_to tup =
        let subst = Subst.add_list ~subst:Subst.empty args tup in
        eval_body subst body
      in
      (* set of tuples on which the function is defined *)
      let dom_tuples = ID.Tbl.to_list dom.dom_args |> List.map snd in
        (* default case: undefined
          TODO: if initial domain was finite, this might be unecessary,
            because CVC4 could model the whole domain? *)
        let default = U.undefined_ (U.app (U.const f_id) (List.map U.var args)) in
        let new_body = List.fold_left
          (fun else_ tup ->
            U.ite
              (U.and_ (List.map2 (fun v t -> U.eq (U.var v) t) args tup))
              (apply_to tup)
              else_)
          default dom_tuples
        in
        List.fold_right U.fun_ args new_body
    in
    (* now remove projections and filter recursion functions's values *)
    Model.filter_map m
      ~terms:(fun (t,u) -> match T.repr t with
        | TI.Const id when ID.Tbl.mem state.approx_fun id ->
            None (* drop approximation functions *)
        | TI.Const f_id when ID.Tbl.mem state.encoded_fun f_id ->
            (* remove junk from the definition of [t] *)
            let u' = decode_fun_ f_id (ID.Tbl.find doms f_id) u in
            Utils.debugf ~section 3 "@[<2>decoding of recursive fun@ %a := `@[%a@]`@ is `@[%a@]`@]"
              (fun k->k ID.print f_id P.print u P.print u');
            Some (t, u')
        | _ -> Some (t,u))
      ~finite_types:(fun ((ty,_) as pair) -> match T.repr ty with
        | TI.Const id when ID.Tbl.mem state.abstract_ty id ->
            None (* remove abstraction types *)
        | _ -> Some pair)

  let decode_model ~state m =
    let projs, domains = pass1_ ~state m in
    Utils.debugf ~section 2 "@[<2>domains:@ @[%a@]@]"
      (fun k->k (CCFormat.seq ~start:"" ~stop:"" pp_domain) (ID.Tbl.values domains));
    pass2_ projs domains;
    pass3_ ~state domains m

  (** {6 Pipe} *)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of recursion: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name:"recursion_elim"
      ~encode:(fun p ->
        let p, state = elim_recursion p in
        p, state
      )
      ~decode
      ()

  let pipe ~print =
    let decode state m = decode_model ~state m in
    pipe_with ~print ~decode
end
