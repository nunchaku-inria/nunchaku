
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Callback = Utils.Callback
module Subst = Var.Subst
module T = Term
module PStmt = Statement.Print(T)(T)
module TyP = TypePoly
module TyM = TypeMono.Default

let name = "mono"
let section = Utils.Section.make name

type term = T.t

exception InvalidProblem of string

let fpf = Format.fprintf

let () = Printexc.register_printer
    (function
      | InvalidProblem msg ->
        Some (Utils.err_sprintf "monomorphization:@ invalid problem:@ %s" msg)
      | _ -> None
    )

let fail_ msg = raise (InvalidProblem msg)
let failf_ msg = Utils.exn_ksprintf msg ~f:fail_

let pp_ty = T.pp
let pp_term = T.pp

(* A tuple of arguments that a given function symbol should be
   instantiated with *)
module ArgTuple = struct
  type t = {
    args: term list; (** Type arguments, before being processed *)
    m_args: term list; (** Type arguments, processed (and possibly mangled) *)
    mangled: ID.t option; (* mangled name of [f args] *)
  }

  let empty = {args=[]; m_args=[]; mangled=None;}
  let make ~mangled ~args ~m_args = {mangled; args; m_args; }
  let length t = List.length t.args
  let args t = t.args
  let m_args t = t.m_args
  let mangled t = t.mangled

  (* equality for ground atomic types T.t *)
  let rec ty_ground_eq_ t1 t2 = match TyM.repr t1, TyM.repr t2 with
    | TyM.Builtin b1, TyM.Builtin b2 -> TI.TyBuiltin.equal b1 b2
    | TyM.Const id1, TyM.Const id2 -> ID.equal id1 id2
    | TyM.App (f1,l1), TyM.App (f2,l2) ->
      ty_ground_eq_ f1 f2 && CCList.equal ty_ground_eq_ l1 l2
    | TyM.Arrow (a1,b1), TyM.Arrow (a2,b2) ->
      ty_ground_eq_ a1 a2 && ty_ground_eq_ b1 b2
    | TyM.Const _, _
    | TyM.App _, _
    | TyM.Builtin _, _
    | TyM.Arrow _, _ -> false

  let equal tup1 tup2 =
    CCList.equal ty_ground_eq_ tup1.args tup2.args

  (* [app_poly_ty ty arg] applies polymorphic type [ty] to type parameters [arg] *)
  let app_poly_ty ty arg =
    let tys = List.map (fun _ -> T.ty_type) arg.m_args in
    let ty, subst = T.ty_apply_full ty ~terms:arg.m_args ~tys in
    T.eval ~subst ty, subst

  let pp out tup =
    let pp_mangled out = function
      | None -> ()
      | Some id -> fpf out " as %a" ID.pp id
    in
    fpf out "(@[%a%a@])"
      (Utils.pp_list ~sep:", " pp_ty) tup.args
      pp_mangled tup.mangled
end

type unmangle_state = (ID.t * term list) ID.Tbl.t
(* used for unmangling *)

module St = struct
  type t = {
    always_mangle: bool;
    mangle : (string, ID.t) Hashtbl.t;
    (* mangled name -> mangled ID *)
    unmangle : unmangle_state;
    (* mangled name -> (id, args) *)
  }

  let create ~always_mangle () = {
    always_mangle;
    mangle=Hashtbl.create 64;
    unmangle=ID.Tbl.create 64;
  }

  let always_mangle st = st.always_mangle

  (* remember that (id,tup) -> mangled *)
  let save_mangled ~state id tup ~mangled =
    try Hashtbl.find state.mangle mangled
    with Not_found ->
      (* create new ID *)
      let mangled' = ID.make mangled in
      Utils.debugf ~section 5
        "@[<2>save_mangled %a@ for %a (@[%a@])@]"
        (fun k->k ID.pp mangled' ID.pp id (CCFormat.list T.pp) tup);
      Hashtbl.add state.mangle mangled mangled';
      ID.Tbl.replace state.unmangle mangled' (id, tup);
      mangled'
end

(* use the generic traversal *)
module Trav = Traversal.Make(T)(struct
    type t = ArgTuple.t
    let equal = ArgTuple.equal
    let hash _ = 0
    let pp = ArgTuple.pp
    let section = section
    let fail = failf_
  end)(St)

(* find a specialized name for [id tup] if [tup] not empty.
   returns ID to use, and [Some mangled] if [args <> []], None otherwise
   (so it can be used in [!ArgTuple.of_list ~mangled]).
   @param args already mangled arguments *)
let mangle_ ~state id (args:term list) =
  match args with
    | [] -> id, None
    | _::_ ->
      let name = TyM.mangle ~sep:"_" (T.app_const id args) in
      let mangled = St.save_mangled ~state id args ~mangled:name in
      mangled, Some mangled

(* should [id] be mangled? in all cases, yes, except if it's an
   uninterpreted or copy type. *)
let should_be_mangled_ ~env id =
  match Env.find_exn ~env id with
    | {Env.def=(Env.Fun_def _ | Env.Fun_spec _ |
                Env.Cstor _ | Env.Data _ | Env.Pred _ |
                Env.Copy_abstract _ | Env.Copy_concrete _ |
                Env.Copy_ty _); _} ->
      true (* defined objects: mangle *)
    | {Env.def=Env.NoDef; ty; _} when T.ty_returns_Type ty ->
      false (* uninterpreted poly types: do not mangle *)
    | {Env.def=Env.NoDef; _} ->
      true (* functions and prop: mangle *)

(* bind the type variables of [def] to [tup]. *)
let match_rec ?(subst=Subst.empty) ~def tup =
  assert (ArgTuple.length tup = List.length def.Stmt.rec_ty_vars);
  Subst.add_list ~subst def.Stmt.rec_ty_vars (ArgTuple.m_args tup)

(* bind the type variables of [spec] to [tup]. *)
let match_spec ?(subst=Subst.empty) ~spec tup =
  assert (ArgTuple.length tup = List.length spec.Stmt.spec_ty_vars);
  Subst.add_list ~subst spec.Stmt.spec_ty_vars (ArgTuple.m_args tup)

(* bind the type variables of [def] to [tup]. *)
let match_pred ?(subst=Subst.empty) ~(def:(_,_) Stmt.pred_def) tup =
  assert (ArgTuple.length tup = List.length def.Stmt.pred_tyvars);
  Subst.add_list ~subst def.Stmt.pred_tyvars (ArgTuple.m_args tup)

(* local state for monomorphization, used in recursive traversal of terms *)
type local_state = {
  depth: int;
  subst: (term,term) Subst.t;
}

(* monomorphize term *)
let rec mono_term ~self ~local_state (t:term) : term =
  Utils.debugf ~section 5 "@[<2>mono term@ `@[%a@]`@]" (fun k->k T.pp t);
  match T.repr t with
    | TI.Builtin b ->
      T.builtin (Builtin.map b ~f:(mono_term ~self ~local_state))
    | TI.Const c ->
      (* no args, but we require [c, ()] in the output *)
      let depth = local_state.depth+1 in
      Trav.call_dep self ~depth c ArgTuple.empty;
      T.const c
    | TI.Var v ->
      begin match Subst.find ~subst:local_state.subst v with
        | Some t' -> mono_term ~self ~local_state t'
        | None ->
          T.var (mono_var ~self ~local_state v)
      end
    | TI.App (f,l) ->
      (* first, beta-reduce locally; can possibly enrich [subst] *)
      let f, l, subst, guard = T.Red.Full.whnf ~subst:local_state.subst f l in
      let local_state = {local_state with subst; } in
      let t' = match T.repr f with
        | TI.Bind (Binder.Fun, _, _) when l<>[] -> assert false (* beta-reduction failed? *)
        | TI.Builtin _ ->
          (* builtins are defined, but examine their args *)
          let f = mono_term ~self ~local_state f in
          let l = List.map (mono_term ~self ~local_state) l in
          T.guard (T.app f l) guard
        | TI.Const id ->
          (* find type arguments *)
          let info = Env.find_exn ~env:(Trav.env self) id in
          let ty = info.Env.ty in
          if T.ty_returns_Type ty
          && Env.is_not_def info
          && not (St.always_mangle (Trav.state self))
          then (
            (* do not change undefined type constructors, such as [pair],
               keep them parametric; do not mangle (unless [always_mangle=true])! *)
            Trav.call_dep self ~depth:local_state.depth id ArgTuple.empty;
            let l' = List.map (mono_type ~self ~local_state) l in
            T.app_const id l'
          ) else (
            let n = T.ty_num_param ty in
            (* tuple of arguments for [id], not encoded yet *)
            let unmangled_tup = take_n_ground_atomic_types_ ~self ~local_state n l in
            let mangled_tup = List.map (mono_type ~self ~local_state) unmangled_tup in
            (* mangle? *)
            let new_id, mangled =
              if St.always_mangle (Trav.state self)
              || should_be_mangled_ ~env:(Trav.env self) id
              then mangle_ ~state:(Trav.state self) id mangled_tup
              else id, None
            in
            (* specialize [id] *)
            let tup =
              ArgTuple.make ~mangled ~args:unmangled_tup ~m_args:mangled_tup in
            let depth = local_state.depth + 1 in
            Trav.call_dep self ~depth id tup;
            (* convert arguments.
               Drop type arguments iff they are mangled with ID *)
            let l = if mangled=None then l else CCList.drop n l in
            let l = List.map (mono_term ~self ~local_state) l in
            T.app_const new_id l
          )
        | TI.Var v ->
          (* allow variables in head (in spec/rec and in functions) *)
          begin match Subst.find ~subst:local_state.subst v with
            | None ->
              let v = mono_var ~self ~local_state v in
              let l = List.map (mono_term ~self ~local_state) l in
              T.app (T.var v) l
            | Some t ->
              mono_term ~self ~local_state (T.app t l)
          end
        | _ ->
          T.app
            (mono_term ~self ~local_state f)
            (List.map (mono_term ~self ~local_state) l)
      in
      T.guard t' guard
    | TI.Bind ((Binder.Fun | Binder.Forall | Binder.Exists | Binder.Mu) as b, v, t) ->
      T.mk_bind b
        (mono_var ~self ~local_state v)
        (mono_term ~self ~local_state t)
    | TI.Let (v,t,u) ->
      T.let_ (mono_var ~self ~local_state v)
        (mono_term ~self ~local_state t)
        (mono_term ~self ~local_state u)
    | TI.Match (t,l,def) ->
      let t = mono_term ~self ~local_state t in
      let def = TI.map_default_case (mono_term ~self ~local_state) def in
      let l =
        ID.Map.to_iter l
        |> Iter.map
          (fun (c, (tys, vars,rhs)) ->
            let mangled_tys = List.map (mono_type ~self ~local_state) tys in
            let c' =
              if St.always_mangle (Trav.state self)
              || should_be_mangled_ ~env:(Trav.env self) c
              then fst @@ mangle_ ~state:(Trav.state self) c mangled_tys
              else c
            in
            let vars = List.map (mono_var ~self ~local_state) vars in
            c', ([], vars, mono_term ~self ~local_state rhs))
        |> ID.Map.of_iter
      in
      T.match_with t l ~def
    | TI.TyBuiltin b -> T.ty_builtin b
    | TI.TyArrow (a,b) ->
      T.ty_arrow
        (mono_term ~self ~local_state a)
        (mono_term ~self ~local_state b)
    | TI.TyMeta _ -> assert false
    | TI.Bind (Binder.TyForall,_,_) ->
      failf_ "@[<2>cannot monomorphize quantified type@ @[%a@]@]" pp_ty t

and mono_var ~self ~local_state v : term Var.t =
  Var.update_ty v ~f:(mono_type ~self ~local_state)

and mono_type ~self ~local_state t : term =
  mono_term ~self ~local_state t

(* take [n] ground atomic type arguments in [l], or fail *)
and take_n_ground_atomic_types_ ~self ~local_state n = function
  | _ when n=0 -> []
  | [] -> failf_ "not enough arguments (%d missing)" n
  | t :: l' ->
    T.eval ~subst:local_state.subst t
    :: take_n_ground_atomic_types_ ~self ~local_state (n-1) l'

(* some type variable? *)
let term_has_ty_vars t =
  T.to_seq_vars t
  |> Iter.exists (fun v -> T.ty_is_Type (Var.ty v))

let mono_defined ~self ~local_state d tup =
  let ty, _ = ArgTuple.app_poly_ty d.Stmt.defined_ty tup in
  let new_ty = mono_type ~self ~local_state ty in
  let state = Trav.state self in
  let new_id, _ =
    mangle_ ~state d.Stmt.defined_head (ArgTuple.m_args tup)
  in
  Stmt.mk_defined ~attrs:[] new_id new_ty

(* monomorphize equations properly
   n: number of type arguments *)
let mono_eqns
  : self:Trav.t -> local_state:local_state -> int ->
  (_,_) Stmt.equations -> (_,_) Stmt.equations
  = fun ~self ~local_state n eqn ->
    let f e =
      Stmt.map_eqns e
        ~term:(mono_term ~self ~local_state)
        ~ty:(mono_type ~self ~local_state)
    in
    match eqn with
      | Stmt.Eqn_nested l ->
        f (Stmt.Eqn_nested
            (List.map
               (fun (vars, args, rhs, side) -> vars, CCList.drop n args, rhs, side)
               l))
      | Stmt.Eqn_single (vars, rhs) ->
        let vars = CCList.drop n vars in
        Stmt.Eqn_single (vars, mono_term ~self ~local_state rhs)
      | Stmt.Eqn_app _ -> assert false

let mk_local_state ?(subst=Subst.empty) depth =
  { subst; depth; }

let dispatch = {
  Trav.
  do_term = (fun self ~depth t ->
    let local_state = mk_local_state depth in
    mono_term ~self ~local_state t
  );

  do_goal_or_axiom = None;

  (* specialize mutual recursive definitions *)
  do_def = (fun self ~depth def arg ->
    Utils.debugf ~section 5 "monomorphize def %a on %a"
      (fun k->k ID.pp def.Stmt.rec_defined.Stmt.defined_head ArgTuple.pp arg);
    let subst = match_rec ~def arg in
    (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
    let local_state = mk_local_state ~subst (depth+1) in
    let n = List.length def.Stmt.rec_ty_vars in
    let eqns = mono_eqns ~self ~local_state n def.Stmt.rec_eqns in
    (* new (specialized) case *)
    let rec_defined = mono_defined ~self ~local_state def.Stmt.rec_defined arg in
    let def' =
      {Stmt.
        rec_ty_vars=[];
        rec_defined;
        rec_eqns=eqns;
      } in
    def'
  );

  do_pred = (fun self ~depth _ _ def arg ->
    Utils.debugf ~section 5 "monomorphize pred %a on %a"
      (fun k->k ID.pp def.Stmt.pred_defined.Stmt.defined_head ArgTuple.pp arg);
    let subst = match_pred ~def arg in
    (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
    let local_state = mk_local_state ~subst (depth+1) in
    let clauses =
      List.map
        (Stmt.map_clause
           ~term:(mono_term ~self ~local_state)
           ~ty:(mono_term ~self ~local_state))
        def.Stmt.pred_clauses
    in
    (* new (specialized) case *)
    let pred_defined = mono_defined ~self ~local_state
        def.Stmt.pred_defined arg in
    let def' =
      {Stmt.
        pred_tyvars=[];
        pred_defined;
        pred_clauses=clauses;
      } in
    def'
  );

  (* specialize specification *)
  do_spec =
    Some (fun self ~depth ~loc:_ id spec tup ->
      Utils.debugf ~section 5 "monomorphize spec for %a on %a"
        (fun k->k ID.pp id ArgTuple.pp tup);
      assert (ArgTuple.length tup = List.length spec.Stmt.spec_ty_vars);
      let st = Trav.state self in
      (* flag every symbol as specialized. We can use [tup] for every
           specified symbol, as they all share the same set of type variables. *)
      let subst = match_spec ~spec tup in
      List.iter
        (fun d ->
           let id' = d.Stmt.defined_head in
           let _, mangled = mangle_ ~state:st id' (ArgTuple.m_args tup) in
           let tup' = ArgTuple.make
               ~mangled
               ~args:(ArgTuple.args tup)
               ~m_args:(ArgTuple.m_args tup) in
           Utils.debugf ~section 4 "@[<2>specialization of `@[<2>%a@ %a@]` is done@]"
             (fun k -> k ID.pp id' ArgTuple.pp tup');
           Trav.mark_processed self id' tup';
        )
        spec.Stmt.spec_defined;
      (* convert axioms and defined terms *)
      let local_state = mk_local_state ~subst depth in
      let defined = List.map
          (fun d -> mono_defined ~self ~local_state d tup)
          spec.Stmt.spec_defined
      and axioms = List.map
          (fun ax -> mono_term ~self ~local_state ax)
          spec.Stmt.spec_axioms
      in
      let st' = {Stmt.spec_axioms=axioms; spec_defined=defined; spec_ty_vars=[]; } in
      st'
    );

  do_data = Some (fun self ~depth _ tydef tup ->
      (* mangle type name. Monomorphized type should be : Type *)
      let st = Trav.state self in
      let id, mangled =
        mangle_ ~state:st tydef.Stmt.ty_id (ArgTuple.m_args tup) in
      let tup = {tup with ArgTuple.mangled; } in
      Utils.debugf ~section 5 "monomorphize data %a on %a"
        (fun k->k ID.pp tydef.Stmt.ty_id ArgTuple.pp tup);
      let ty = T.ty_type in
      (* specialize each constructor *)
      let cstors = ID.Map.fold
          (fun _ c acc ->
             (* mangle ID *)
             let id', mangled = mangle_ ~state:st c.Stmt.cstor_name (ArgTuple.m_args tup) in
             let tup' = {tup with ArgTuple.mangled; } in
             (* apply, then convert type. Arity should match. *)
             let ty', subst = ArgTuple.app_poly_ty c.Stmt.cstor_type tup' in
             Utils.debugf ~section 5 "@[<hv2>monomorphize cstor `@[%a@ : %a@]`@ with @[%a@]@]"
               (fun k->k ID.pp id' T.pp ty' (Subst.pp T.pp) subst);
             (* convert type and substitute in it *)
             let local_state = mk_local_state ~subst (depth+1) in
             let ty' = mono_term ~self ~local_state ty' in
             let args' = List.map (mono_term ~self ~local_state) c.Stmt.cstor_args in
             let c' = { Stmt.cstor_name=id'; cstor_type=ty'; cstor_args=args'; } in
             ID.Map.add id' c' acc)
          tydef.Stmt.ty_cstors
          ID.Map.empty
      in
      (* add monomorphized type to [res] *)
      let tydef' =
        {Stmt.
          ty_id=id; ty_type=ty; ty_cstors=cstors; ty_vars=[];
        } in
      tydef'
    );

  (* monomorphize the given copy type *)
  do_copy = Some (fun self ~depth ~loc:_ c tup ->
      assert (ArgTuple.length tup = List.length c.Stmt.copy_vars);
      let st = Trav.state self in
      Utils.debugf ~section 3
        "@[<2>monomorphize copy type@ `@[%a@]`@ on (%a)@ at depth %d@]"
        (fun k->k PStmt.pp_copy c ArgTuple.pp tup depth);
      (* ensure we do not encode this several times, from type/abstract/concrete *)
      Trav.mark_processed self c.Stmt.copy_id tup;
      Trav.mark_processed self c.Stmt.copy_abstract tup;
      Trav.mark_processed self c.Stmt.copy_concrete tup;
      (* mangle ID, functions and definition, possibly monomorphizing
         other types in the process *)
      let subst =
        Subst.add_list ~subst:Subst.empty
          c.Stmt.copy_vars (ArgTuple.m_args tup)
      in
      let id', _ = mangle_ ~state:st c.Stmt.copy_id (ArgTuple.m_args tup) in
      let local_state = mk_local_state ~subst depth in
      let of_' = mono_type ~self ~local_state c.Stmt.copy_of in
      let to_' = mono_type ~self ~local_state c.Stmt.copy_to in
      let wrt = match c.Stmt.copy_wrt with
        | Stmt.Wrt_nothing -> Stmt.Wrt_nothing
        | Stmt.Wrt_subset p -> Stmt.Wrt_subset (mono_term ~self ~local_state p)
        | Stmt.Wrt_quotient (tty, r) -> Stmt.Wrt_quotient (tty, mono_term ~self ~local_state r)
      in
      let abstract', _ =
        mangle_ ~state:st c.Stmt.copy_abstract (ArgTuple.m_args tup) in
      let concrete', _ =
        mangle_ ~state:st c.Stmt.copy_concrete (ArgTuple.m_args tup) in
      let ty_abstract' = T.ty_arrow of_' to_' in
      let ty_concrete' = T.ty_arrow to_' of_' in
      let ty' = T.ty_type in
      (* create new copy type *)
      let c' =
        Stmt.mk_copy
          ~of_:of_' ~to_:to_' ~ty:ty' ~vars:[]
          ~wrt
          ~abstract:(abstract', ty_abstract')
          ~concrete:(concrete', ty_concrete')
          id'
      in
      c'
    );

  (* declare a symbol that is axiomatized *)
  do_ty_def = Some (fun self ?loc:_ d tup ->
      let id = Stmt.id_of_defined d in
      Utils.debugf ~section 5 "declare type for %a on %a"
        (fun k->k ID.pp id ArgTuple.pp tup);
      (* declare specialized type *)
      let new_id = match ArgTuple.mangled tup with
        | None -> id
        | Some x -> x
      in
      let ty, subst = ArgTuple.app_poly_ty (Stmt.ty_of_defined d) tup in
      let local_state = mk_local_state ~subst 0 in
      let new_ty = mono_type ~self ~local_state ty in
      Stmt.mk_defined ~attrs:(Stmt.attrs_of_defined d) new_id new_ty
    );
}

(* TODO: gather by ID first *)
let pp_processed_ out trav =
  Trav.processed trav
  |> Format.fprintf out "@[<v>%a@]"
    (Utils.pp_seq ~sep:""
       (fun out (id,tup) ->
          Format.fprintf out "@[<h>%a (%a)@]" ID.pp id ArgTuple.pp tup))

let mono_statement t st =
  begin match Stmt.view st with
    | Stmt.Goal t ->
      if term_has_ty_vars t
      then failf_ "goal `@[%a@]` contains type variables" T.pp t
    | _ -> ()
  end;
  Trav.traverse_stmt t st

let monomorphize ?(depth_limit=256) ?(always_mangle=false) pb =
  let state = St.create ~always_mangle () in
  (* create the state used for monomorphization. Toplevel function
     for specializing (id,tup) is [mono_statements_for_id] *)
  let traverse = Trav.create
      ~max_depth:depth_limit
      ~env:(Env.create ())
      ~state
      ~dispatch
      ()
  in
  (* iterate on statements *)
  CCVector.iter (mono_statement traverse) (Problem.statements pb);
  (* output result. If depth limit reached we might be incomplete *)
  let meta =
    Problem.metadata pb
    |> ProblemMetadata.add_sat_means_unknown
      (Trav.max_depth_reached traverse)
  in
  let res = Trav.get_statements traverse |> CCVector.freeze in
  let pb' = Problem.make ~meta res in
  (* some debug *)
  Utils.debugf ~section 3 "@[<2>instances:@ @[%a@]@]"
    (fun k-> k pp_processed_ traverse);
  pb', state.St.unmangle

(** {6 Decoding} *)

let unmangle_term ~(state:unmangle_state) (t:term):term =
  let rec aux t = match T.repr t with
    | TI.Var v -> T.var (aux_var v)
    | TI.Const id ->
      begin try
          let id', args = ID.Tbl.find state id in
          T.app (T.const id') (List.map aux args)
        with Not_found -> T.const id
      end
    | TI.App (f,l) -> T.app (aux f) (List.map aux l)
    | TI.Builtin b -> T.builtin (Builtin.map b ~f:aux)
    | TI.Bind ((Binder.Forall | Binder.Exists | Binder.Fun | Binder.Mu) as b,v,t) ->
      T.mk_bind b (aux_var v) (aux t)
    | TI.Let (v,t,u) -> T.let_ (aux_var v) (aux t) (aux u)
    | TI.Match (t,l,def) ->
      let t = aux t in
      let def = TI.map_default_case aux def in
      let l =
        ID.Map.to_iter l
        |> Iter.map
          (fun (c,(tys,vars,rhs)) ->
            assert (tys=[]);
            let vars = List.map aux_var vars in
            let rhs = aux rhs in
            begin try
                let c', tys = ID.Tbl.find state c in
                c', (tys,vars,rhs)
              with Not_found -> c, ([],vars,rhs)
            end)
        |> ID.Map.of_iter
      in
      T.match_with t l ~def
    | TI.TyBuiltin b -> T.ty_builtin b
    | TI.TyArrow (a,b) -> T.ty_arrow (aux a) (aux b)
    | TI.Bind (Binder.TyForall, _,_) | TI.TyMeta _ -> assert false
  and aux_var v = Var.update_ty ~f:aux v in
  aux t

(* rewrite mangled constants to their definition *)
let unmangle_model ~state =
  Model.map ~term:(unmangle_term ~state) ~ty:(unmangle_term ~state)

let pipe_with ~decode ~always_mangle ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module PPb = Problem.P in
        Format.printf "@[<v2>@{<Yellow>after mono@}: %a@]@." PPb.pp)
    @
      Utils.singleton_if check ()
        ~f:(fun () ->
          let module C = TypeCheck.Make(T) in
          let t = C.empty ~check_non_empty_tys:true () in
          C.check_problem t)
  in
  Transform.make
    ~on_encoded
    ~input_spec:Transform.Features.(empty |> update Ty Poly)
    ~map_spec:Transform.Features.(update Ty Mono)
    ~name
    ~encode:(fun p -> monomorphize ~always_mangle p)
    ~decode
    ()

let pipe ~always_mangle ~print ~check =
  let decode state = Problem.Res.map_m ~f:(unmangle_model ~state) in
  pipe_with ~always_mangle ~print ~decode ~check
