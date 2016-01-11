
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = ID
module Var = Var
module TI = TermInner
module TyI = TypeMono
module Stmt = Statement
module Sig = Signature

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
    subst: (term,term) Subst.t;
      (* local substitution *)
  }

  let empty_local_state = {subst=Subst.empty; }

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match TyM.repr ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

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

  (* translate term/formula recursively into a new (guarded) term. *)
  let rec tr_term_rec_ ~state ~local_state (t:term) : term =
    match T.repr t with
    | TI.Const _ -> t
    | TI.Var v ->
        (* substitute if needed; no side-condition *)
        begin match Subst.find ~subst:local_state.subst v with
          | None -> t
          | Some t' -> t'
        end
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
              let eqns = ref [] in
              let l' = List.map2
                (fun arg (proj,_ty_proj) ->
                  (* under a function: no polarity *)
                  let arg' = tr_term_rec_ arg ~state ~local_state in
                  let eqn = U.eq arg' (U.app (U.const proj) [U.var alpha]) in
                  eqns := eqn :: !eqns;
                  arg'
                )
                l
                fundef.fun_concretization
              in
              let cond = U.exists alpha (U.and_ !eqns) in
              U.asserting (U.app f l') [cond]
          | None, TI.Builtin `Not, [t] ->
              let t = tr_term_rec_ ~state ~local_state t in
              U.not_ t
          | None, TI.Builtin ((`Or | `And) as b), l ->
              let l = List.map (tr_term_rec_ ~state ~local_state) l in
              U.app_builtin b l
          | None, TI.Builtin `Imply, [a;b] ->
              let a = tr_term_rec_ ~state ~local_state a in
              let b = tr_term_rec_ ~state ~local_state b in
              U.imply a b
          | None, TI.Builtin ((`DataTest _ | `DataSelect _) as b), [t] ->
              let t' = tr_term_rec_ ~state ~local_state t in
              U.app_builtin b [t']
          | None, _, _ ->
              (* combine side conditions from every sub-term *)
              let l' = List.map
                (tr_term_rec_ ~state ~local_state)
                l
              in
              U.app f l'
        end
    | TI.Builtin (`True | `False
        | `And | `Or | `Not | `Imply | `DataSelect _ | `DataTest _) ->
          t (* partially applied, or constant *)
    | TI.Builtin (`Undefined _ as b) ->
        U.builtin (TI.Builtin.map b ~f:(tr_term_rec_ ~state ~local_state))
    | TI.Builtin (`Guard (t, g)) ->
        let t = tr_term_rec_ ~state ~local_state t in
        let g' = TI.Builtin.map_guard (tr_term_rec_ ~state ~local_state) g in
        U.guard t g'
    | TI.Builtin (`Equiv _) -> fail_tr_ t "cannot translate equivalence (polarity)"
    | TI.Builtin (`Eq (a,b)) ->
        let a = tr_term_rec_ ~state ~local_state a in
        let b = tr_term_rec_ ~state ~local_state b in
        U.eq a b
    | TI.Builtin (`Ite (a,b,c)) ->
        let a = tr_term_rec_ ~state ~local_state a in
        let b = tr_term_rec_ ~state ~local_state b in
        let c = tr_term_rec_ ~state ~local_state c in
        U.ite a b c
    | TI.Bind (`Forall,v,t) ->
        let t' = tr_term_rec_ ~state ~local_state t in
        U.forall v t'
    | TI.Bind (`Exists,v,t) ->
        let t = tr_term_rec_ ~state ~local_state t in
        U.exists v t
    | TI.Bind (`Fun,_,_) -> fail_tr_ t "translation of λ impossible"
    | TI.Let (v,t,u) ->
        (* rename [v] *)
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst:local_state.subst v (U.var v') in
        let t = tr_term_rec_ t ~state ~local_state:{subst;} in
        let u = tr_term_rec_ u ~state ~local_state:{subst;} in
        U.let_ v' t u
    | TI.Match (t, l) ->
        let t = tr_term_rec_ ~state ~local_state t in
        let l = ID.Map.map
          (fun (vars,rhs) -> vars, tr_term_rec_ ~state ~local_state rhs)
          l
        in
        U.match_with t l
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t
    | TI.Bind (`TyForall, _, _)
    | TI.TyMeta _ -> assert false

  let tr_term ~state ~local_state t =
    Utils.debugf ~section 4
      "@[<2>convert toplevel term@ `@[%a@]`@]" (fun k -> k P.print t);
    tr_term_rec_ ~state ~local_state t

  (* translate a top-level formula *)
  let tr_form ~state t =
    tr_term ~state ~local_state:empty_local_state t

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
    let local_state = { subst; } in
    (* convert right-hand side and add its side conditions *)
    let lhs = U.app (U.const fun_encoding.fun_encoded_fun) args' in
    let rhs' = tr_term ~state ~local_state rhs in
    let mk_eq = if U.ty_returns_Prop ty then U.equiv else U.eq in
    U.forall alpha (mk_eq lhs rhs')

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
         concrete arguments it corresponds to *)
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

  type proj_fun = {
    proj_var: T.t Var.t;
      (* argument to the projection function *)

    proj_tree: (T.t, T.t) Model.decision_tree;
      (* decision tree for the variable *)
  }

  module DT_util = Model.DT_util(T)

  (*
     - gather definitions of projections
     - gather domains of abstract types
  *)
  let pass1_ ~state m =
    let projs : proj_fun ID.Tbl.t = ID.Tbl.create 16 in
    let doms  : finite_domain ID.Tbl.t = ID.Tbl.create 16 in
    Model.iter m
      ~constants:(fun (t,_) -> match T.repr t with
        | TI.Const id ->
            (* a function should not be modeled by a constant *)
            assert (not (ID.Tbl.mem state.approx_fun id));
        | _ -> ())
      ~funs:(fun (t,vars,body) -> match T.repr t, vars with
        | TI.Const id, [v] ->
            (* register the model for this approximated function *)
            if ID.Tbl.mem state.approx_fun id
            then ID.Tbl.add projs id {proj_var=v; proj_tree=body; }
        | _, _ -> ())
      ~finite_types:(fun (ty,dom) -> match T.repr ty with
        | TI.Const id ->
            begin try
              let dom_fun = ID.Tbl.find state.abstract_ty id in
              let dom = {dom_fun; dom_dom=dom; dom_args=ID.Tbl.create 16; } in
              ID.Tbl.add doms dom_fun.fun_encoded_fun dom
            with Not_found -> ()
            end
        | _ -> ());
      projs, doms

  (* compute map `abstract type -> set of tuples by projection`.
   Update doms. *)
  let pass2_ projs (doms:finite_domains) =
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
                let subst = Var.Subst.singleton proj.proj_var (U.const val_id) in
                DT_util.eval ~subst proj.proj_tree)
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
    (* decode a function. *)
    let decode_fun_ f_id dom vars body =
      let arity = List.length dom.dom_fun.fun_concretization in
      if List.length vars <> arity
        then fail_decode_
          ~term:(U.fun_l vars (DT_util.to_term body))
          "expected a function of %d arguments" arity;
      (* compute value of the function applied to [tup] *)
      let apply_to tup =
        let subst = Subst.add_list ~subst:Subst.empty vars tup in
        DT_util.eval ~subst body
      in
      (* set of tuples on which the function is defined *)
      let dom_tuples = ID.Tbl.to_list dom.dom_args |> List.map snd in
        (* default case: undefined
          TODO: if initial domain was finite, this might be unecessary,
            because CVC4 could model the whole domain? *)
      let default = U.undefined_ (U.app (U.const f_id) (List.map U.var vars)) in
      let new_body =
        List.map
          (fun tup ->
            let test = List.combine vars tup in
            let then_ = apply_to tup in
            test, Model.DT.yield then_)
          dom_tuples
      in
      Model.DT.test new_body ~else_:default
    in
    (* now remove projections and filter recursion functions's values *)
    Model.filter_map m
      ~constants:(fun (t,u) -> match T.repr t with
        | TI.Const id when ID.Tbl.mem state.approx_fun id ->
            None (* drop approximation functions *)
        | _ -> Some (t,u))
      ~funs:(fun (t,vars,body) -> match T.repr t with
        | TI.Const id when ID.Tbl.mem state.approx_fun id ->
            None (* drop approximation functions *)
        | TI.Const f_id when ID.Tbl.mem state.encoded_fun f_id ->
            (* remove junk from the definition of [t] *)
            let body' = decode_fun_ f_id (ID.Tbl.find doms f_id) vars body in
            Utils.debugf ~section 3
              "@[<hv2>decoding of recursive fun @[%a %a@] :=@ `@[%a@]`@ is `@[%a@]`@]"
              (fun k->k ID.print f_id (CCFormat.list Var.print_full) vars
              (Model.DT.print P.print) body (Model.DT.print P.print) body');
            Some (t, vars, body')
        | _ ->
            (* keep *)
            Some (t,vars,body))
      ~finite_types:(fun ((ty,_) as pair) -> match T.repr ty with
        | TI.Const id when ID.Tbl.mem state.abstract_ty id ->
            None (* remove abstraction types *)
        | _ -> Some pair)

  let decode_model ~state m =
    let projs, domains = pass1_ ~state m in
    pass2_ projs domains;
    Utils.debugf ~section 2 "@[<2>domains:@ @[%a@]@]"
      (fun k->k (CCFormat.seq ~start:"" ~stop:"" pp_domain) (ID.Tbl.values domains));
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
