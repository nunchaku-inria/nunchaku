
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Callback = Utils.Callback
module Subst = Var.Subst
module T = TI.Default
module U = T.U
module P = T.P
module PStmt = Statement.Print(P)(P)
module TyP = TypePoly
module TyM = TypeMono.Make(T)
module TyMI = TypeMono

(* evaluation *)
module Red = Reduce.Make(T)

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

let print_ty = P.print
let print_term = P.print

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
    | TyMI.Builtin b1, TyMI.Builtin b2 -> TI.TyBuiltin.equal b1 b2
    | TyMI.Const id1, TyMI.Const id2 -> ID.equal id1 id2
    | TyMI.App (f1,l1), TyMI.App (f2,l2) ->
      ty_ground_eq_ f1 f2 && CCList.equal ty_ground_eq_ l1 l2
    | TyMI.Arrow (a1,b1), TyMI.Arrow (a2,b2) ->
      ty_ground_eq_ a1 a2 && ty_ground_eq_ b1 b2
    | TyMI.Const _, _
    | TyMI.App _, _
    | TyMI.Builtin _, _
    | TyMI.Arrow _, _ -> false

  let equal tup1 tup2 =
    CCList.equal ty_ground_eq_ tup1.args tup2.args

  (* [app_poly_ty ty arg] applies polymorphic type [ty] to type parameters [arg] *)
  let app_poly_ty ty arg =
    let tys = List.map (fun _ -> U.ty_type) arg.m_args in
    let ty, subst = U.ty_apply_full ty ~terms:arg.m_args ~tys in
    U.eval ~subst ty, subst

  let print out tup =
    let pp_mangled out = function
      | None -> ()
      | Some id -> fpf out " as %a" ID.print id
    in
    fpf out "@[%a%a@]"
      (CCFormat.list ~start:"(" ~stop:")" ~sep:", " print_ty) tup.args
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
        (fun k->k ID.print mangled' ID.print id (CCFormat.list P.print) tup);
      Hashtbl.add state.mangle mangled mangled';
      ID.Tbl.replace state.unmangle mangled' (id, tup);
      mangled'
end

(* use the generic traversal *)
module Trav = Traversal.Make(T)(struct
    type t = ArgTuple.t
    let equal = ArgTuple.equal
    let hash _ = 0
    let print = ArgTuple.print
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
      let name = TyM.mangle ~sep:"_" (U.app_const id args) in
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
    | {Env.def=Env.NoDef; ty; _} when U.ty_returns_Type ty ->
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
  Utils.debugf ~section 5 "@[<2>mono term@ `@[%a@]`@]" (fun k->k P.print t);
  match T.repr t with
    | TI.Builtin b ->
      U.builtin (TI.Builtin.map b ~f:(mono_term ~self ~local_state))
    | TI.Const c ->
      (* no args, but we require [c, ()] in the output *)
      let depth = local_state.depth+1 in
      Trav.call_dep self ~depth c ArgTuple.empty;
      U.const c
    | TI.Var v ->
      begin match Subst.find ~subst:local_state.subst v with
        | Some t' -> mono_term ~self ~local_state t'
        | None ->
          U.var (mono_var ~self ~local_state v)
      end
    | TI.App (f,l) ->
      (* first, beta-reduce locally; can possibly enrich [subst] *)
      let f, l, subst, guard = Red.Full.whnf ~subst:local_state.subst f l in
      let local_state = {local_state with subst; } in
      let t' = match T.repr f with
        | TI.Bind (`Fun, _, _) -> assert false (* beta-reduction failed? *)
        | TI.Builtin _ ->
          (* builtins are defined, but examine their args *)
          let f = mono_term ~self ~local_state f in
          let l = List.map (mono_term ~self ~local_state) l in
          U.guard (U.app f l) guard
        | TI.Const id ->
          (* find type arguments *)
          let info = Env.find_exn ~env:(Trav.env self) id in
          let ty = info.Env.ty in
          if U.ty_returns_Type ty
          && Env.is_not_def info
          && not (St.always_mangle (Trav.state self))
          then (
            (* do not change undefined type constructors, such as [pair],
               keep them parametric; do not mangle (unless [always_mangle=true])! *)
            Trav.call_dep self ~depth:local_state.depth id ArgTuple.empty;
            let l' = List.map (mono_type ~self ~local_state) l in
            U.app_const id l'
          ) else (
            let n = U.ty_num_param ty in
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
            U.app_const new_id l
          )
        | TI.Var v ->
          (* allow variables in head (in spec/rec and in functions) *)
          begin match Subst.find ~subst:local_state.subst v with
            | None ->
              let v = mono_var ~self ~local_state v in
              let l = List.map (mono_term ~self ~local_state) l in
              U.app (U.var v) l
            | Some t ->
              mono_term ~self ~local_state (U.app t l)
          end
        | _ ->
          failf_ "@[<2>cannot monomorphize application term@ `@[%a@]`@]" print_term t
      in
      U.guard t' guard
    | TI.Bind ((`Fun | `Forall | `Exists | `Mu) as b, v, t) ->
      U.mk_bind b
        (mono_var ~self ~local_state v)
        (mono_term ~self ~local_state t)
    | TI.Let (v,t,u) ->
      U.let_ (mono_var ~self ~local_state v)
        (mono_term ~self ~local_state t)
        (mono_term ~self ~local_state u)
    | TI.Match (t,l) ->
      let t = mono_term ~self ~local_state t in
      let l = ID.Map.map
          (fun (vars,rhs) ->
             let vars = List.map (mono_var ~self ~local_state) vars in
             vars, mono_term ~self ~local_state rhs)
          l
      in
      U.match_with t l
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) ->
      U.ty_arrow
        (mono_term ~self ~local_state a)
        (mono_term ~self ~local_state b)
    | TI.TyMeta _ -> assert false
    | TI.Bind (`TyForall,_,_) ->
      failf_ "@[<2>cannot monomorphize quantified type@ @[%a@]@]" print_ty t

and mono_var ~self ~local_state v : term Var.t =
  Var.update_ty v ~f:(mono_type ~self ~local_state)

and mono_type ~self ~local_state t : term =
  mono_term ~self ~local_state t

(* take [n] ground atomic type arguments in [l], or fail *)
and take_n_ground_atomic_types_ ~self ~local_state n = function
  | _ when n=0 -> []
  | [] -> failf_ "not enough arguments (%d missing)" n
  | t :: l' ->
    U.eval ~subst:local_state.subst t
    :: take_n_ground_atomic_types_ ~self ~local_state (n-1) l'

(* some type variable? *)
let term_has_ty_vars t =
  U.to_seq_vars t
  |> Sequence.exists (fun v -> U.ty_is_Type (Var.ty v))

let mono_defined ~self ~local_state d tup =
  let ty, _ = ArgTuple.app_poly_ty d.Stmt.defined_ty tup in
  let defined_ty = mono_type ~self ~local_state ty in
  let state = Trav.state self in
  let defined_head, _ =
    mangle_ ~state d.Stmt.defined_head (ArgTuple.m_args tup)
  in
  {Stmt.defined_head; defined_ty; }

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
      (fun k->k ID.print def.Stmt.rec_defined.Stmt.defined_head ArgTuple.print arg);
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
      (fun k->k ID.print def.Stmt.pred_defined.Stmt.defined_head ArgTuple.print arg);
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
        (fun k->k ID.print id ArgTuple.print tup);
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
             (fun k -> k ID.print id' ArgTuple.print tup');
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
        (fun k->k ID.print tydef.Stmt.ty_id ArgTuple.print tup);
      let ty = U.ty_type in
      (* specialize each constructor *)
      let cstors = ID.Map.fold
          (fun _ c acc ->
             (* mangle ID *)
             let id', mangled = mangle_ ~state:st c.Stmt.cstor_name (ArgTuple.m_args tup) in
             let tup' = {tup with ArgTuple.mangled; } in
             (* apply, then convert type. Arity should match. *)
             let ty', subst = ArgTuple.app_poly_ty c.Stmt.cstor_type tup' in
             Utils.debugf ~section 5 "@[<hv2>monomorphize cstor `@[%a@ : %a@]`@ with @[%a@]@]"
               (fun k->k ID.print id' P.print ty' (Subst.print P.print) subst);
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
      (fun k->k PStmt.print_copy c ArgTuple.print tup depth);
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
    let ty_abstract' = U.ty_arrow of_' to_' in
    let ty_concrete' = U.ty_arrow to_' of_' in
    let ty' = U.ty_type in
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
  do_ty_def = Some (fun self ?loc:_ ~attrs id ~ty tup ->
    Utils.debugf ~section 5 "declare type for %a on %a"
      (fun k->k ID.print id ArgTuple.print tup);
    (* declare specialized type *)
    let new_id = match ArgTuple.mangled tup with
      | None -> id
      | Some x -> x
    in
    let ty, subst = ArgTuple.app_poly_ty ty tup in
    let local_state = mk_local_state ~subst 0 in
    let new_ty = mono_type ~self ~local_state ty in
    new_id, new_ty, attrs
  );
}

(* TODO: gather by ID first *)
let print_processed_ out trav =
  Trav.processed trav
  |> Format.fprintf out "@[<v>%a@]"
      (CCFormat.seq ~start:"" ~stop:"" ~sep:""
        (fun out (id,tup) ->
          Format.fprintf out "@[<h>%a (%a)@]" ID.print id ArgTuple.print tup))

let mono_statement t st =
  begin match Stmt.view st with
    | Stmt.Goal t ->
      if term_has_ty_vars t
      then failf_ "goal `@[%a@]` contains type variables" P.print t
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
    (fun k-> k print_processed_ traverse);
  pb', state.St.unmangle

(** {6 Decoding} *)

let unmangle_term ~(state:unmangle_state) (t:term):term =
  let rec aux t = match T.repr t with
    | TI.Var v -> U.var (aux_var v)
    | TI.Const id ->
        begin try
          let id', args = ID.Tbl.find state id in
          U.app (U.const id') (List.map aux args)
        with Not_found -> U.const id
        end
    | TI.App (f,l) -> U.app (aux f) (List.map aux l)
    | TI.Builtin b -> U.builtin (TI.Builtin.map b ~f:aux)
    | TI.Bind ((`Forall | `Exists | `Fun | `Mu) as b,v,t) ->
        U.mk_bind b (aux_var v) (aux t)
    | TI.Let (v,t,u) -> U.let_ (aux_var v) (aux t) (aux u)
    | TI.Match (t,l) ->
        let t = aux t in
        let l = ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, aux rhs) l in
        U.match_with t l
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) -> U.ty_arrow (aux a) (aux b)
    | TI.Bind (`TyForall, _,_) | TI.TyMeta _ -> assert false
  and aux_var = Var.update_ty ~f:aux in
  aux t

(* rewrite mangled constants to their definition *)
let unmangle_model ~state =
  Model.map ~term:(unmangle_term ~state) ~ty:(unmangle_term ~state)

let pipe_with ~decode ~always_mangle ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module PPb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after mono@}: %a@]@." PPb.print)
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
