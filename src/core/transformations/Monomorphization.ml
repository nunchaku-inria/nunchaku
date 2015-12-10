
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = ID
module Var = Var
module TI = TermInner
module Stmt = Statement
module Env = Env
module Callback = Utils.Callback
module Subst = Var.Subst

type id = ID.t

let section = Utils.Section.make "mono"

type ('a,'b) inv1 = <ty:[`Poly]; eqn:'a; ind_preds:'b>
type ('a,'b) inv2 = <ty:[`Mono]; eqn:'a; ind_preds:'b>

module Make(T : TI.S) = struct
  module T = T
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Statement.Print(P)(P)

  module TyP = TypePoly
  module TyM = TypeMono.Make(T)
  module TyMI = TypeMono

  type term = T.t

  (* substitution *)
  module Red = Reduce.Make(T)

  exception InvalidProblem of string

  let print_ty = P.print
  let print_term = P.print

  let fpf = Format.fprintf
  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | InvalidProblem msg ->
          Some (spf "@[<2>monomorphization:@ invalid problem:@ %s@]" msg)
      | _ -> None
    )

  let fail_ msg = raise (InvalidProblem msg)
  let failf_ msg = Utils.exn_ksprintf msg ~f:fail_

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

    let print out tup =
      let pp_mangled out = function
        | None -> ()
        | Some id -> fpf out " as %a" ID.print id
      in
      fpf out "@[%a%a@]"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:", " print_ty) tup.args
        pp_mangled tup.mangled
  end

  let find_ty_ ~env id =
    try Env.find_ty_exn ~env id
    with Not_found ->
      failf_ "symbol %a is not declared" ID.print id

  type unmangle_state = (ID.t * term list) ID.Tbl.t
  (* used for unmangling *)

  module St = struct
    type ('a,'b) t = {
      mangle : (string, ID.t) Hashtbl.t;
        (* mangled name -> mangled ID *)
      unmangle : unmangle_state;
        (* mangled name -> (id, args) *)
      mutable fun_: depth:int -> ID.t -> ArgTuple.t -> unit;
        (* specialization function *)
      mutable get_env: unit -> (term, term, ('a,'b) inv1) Env.t;
        (* obtain the current environment *)
    }

    let create () = {
      mangle=Hashtbl.create 64;
      unmangle=ID.Tbl.create 64;
      fun_=(fun ~depth:_ _ _ -> assert false);
      get_env=(fun () -> assert false);
    }

    (* remember that (id,tup) -> mangled *)
    let save_mangled ~state id tup ~mangled =
      try Hashtbl.find state.mangle mangled
      with Not_found ->
        (* create new ID *)
        let mangled' = ID.make mangled in
        Hashtbl.add state.mangle mangled mangled';
        ID.Tbl.replace state.unmangle mangled' (id, tup);
        mangled'

    let call ~state ~depth id tup = state.fun_ ~depth id tup

    let get_env ~state = state.get_env ()
  end

  (* find a specialized name for [id tup] if [tup] not empty.
     returns ID to use, and [Some mangled] if [args <> []], None otherwise
     (so it can be used in [!ArgTuple.of_list ~mangled]).
     @param args already mangled arguments *)
  let mangle_ ~state id (args:term list) =
    let pp_list p = CCFormat.list ~start:"" ~stop:"" ~sep:"_" p in
    let rec flat_ty_ out (t:term) = match TyM.repr t with
      | TyMI.Builtin b -> CCFormat.string out (TI.TyBuiltin.to_string b)
      | TyMI.Const id -> ID.print_name out id
      | TyMI.App (f,l) ->
          fpf out "%a_%a" flat_ty_ f (pp_list flat_ty_) l
      | TyMI.Arrow (a,b) -> fpf out "%a_to_%a" flat_ty_ a flat_ty_ b
    in
    match args with
    | [] -> id, None
    | _::_ ->
      let name = CCFormat.sprintf "@[<h>%a@]" flat_ty_ (U.app (U.const id) args) in
      let mangled = St.save_mangled ~state id args ~mangled:name in
      mangled, Some mangled

  (* should [id] be mangled? in all cases, yes, except if it's an
     uninterpreted type. *)
  let should_be_mangled_ ~env id =
    match Env.find_exn ~env id with
    | {Env.def=(Env.Fun_def _ | Env.Fun_spec _ |
                Env.Cstor _ | Env.Data _ | Env.Pred _); _} ->
        true (* defined objects: mangle *)
    | {Env.def=Env.NoDef; decl_kind=(Stmt.Decl_fun | Stmt.Decl_prop); _} ->
        true (* functions and prop: mangle *)
    | {Env.def=Env.NoDef; decl_kind=Stmt.Decl_type; _} ->
        false (* uninterpreted poly types: do not mangle *)

  (* bind the type variables of [def] to [tup]. *)
  let match_rec ?(subst=Subst.empty) ~def tup =
    assert (ArgTuple.length tup = List.length def.Stmt.rec_vars);
    Subst.add_list ~subst def.Stmt.rec_vars (ArgTuple.m_args tup)

  (* bind the type variables of [spec] to [tup]. *)
  let match_spec ?(subst=Subst.empty) ~spec tup =
    assert (ArgTuple.length tup = List.length spec.Stmt.spec_vars);
    Subst.add_list ~subst spec.Stmt.spec_vars (ArgTuple.m_args tup)

  (* bind the type variables of [def] to [tup]. *)
  let match_pred (type i) ?(subst=Subst.empty) ~(def:(_,_,i) Stmt.pred_def) tup =
    assert (ArgTuple.length tup = List.length def.Stmt.pred_tyvars);
    Subst.add_list ~subst def.Stmt.pred_tyvars (ArgTuple.m_args tup)

  (* local state for monomorphization, used in recursive traversal of terms *)
  type local_state = {
    depth: int;
    subst: (term,term) Subst.t;
  }

  (* monomorphize term *)
  let rec mono_term ~state ~local_state (t:term) : term =
    match T.repr t with
    | TI.Builtin b ->
        U.builtin (TI.Builtin.map b ~f:(mono_term ~state ~local_state))
    | TI.Const c ->
        (* no args, but we require [c, ()] in the output *)
        let depth = local_state.depth+1 in
        St.call ~state ~depth c ArgTuple.empty;
        U.const c
    | TI.Var v ->
        begin match Subst.find ~subst:local_state.subst v with
        | Some t' -> mono_term ~state ~local_state t'
        | None ->
            U.var (mono_var ~state ~local_state v)
        end
    | TI.App (f,l) ->
        (* first, beta-reduce locally; can possibly enrich [subst] *)
        let f, l, subst = Red.Full.whnf ~subst:local_state.subst f l in
        let local_state = {local_state with subst; } in
        begin match T.repr f with
        | TI.Bind (`Fun, _, _) -> assert false (* beta-reduction failed? *)
        | TI.Builtin _ ->
            (* builtins are defined, but examine their args *)
            let f = mono_term ~state ~local_state f in
            let l = List.map (mono_term ~state ~local_state) l in
            U.app f l
        | TI.Const id ->
            (* find type arguments *)
            let ty = find_ty_ ~env:(St.get_env ~state) id in
            let n = U.ty_num_param ty in
            (* tuple of arguments for [id], not encoded yet *)
            let unmangled_tup = take_n_ground_atomic_types_ ~state ~local_state n l in
            let mangled_tup = List.map (mono_type ~state ~local_state) unmangled_tup in
            (* mangle? *)
            let new_id, mangled =
              if should_be_mangled_ ~env:(St.get_env ~state) id
              then mangle_ ~state id mangled_tup
              else id, None
            in
            (* specialize [id] *)
            let unmangled_tup = ArgTuple.make
              ~mangled ~args:unmangled_tup ~m_args:mangled_tup in
            let depth = local_state.depth + 1 in
            St.call ~state ~depth id unmangled_tup;
            (* convert arguments.
               Drop type arguments iff they are mangled with ID *)
            let l = if mangled=None then l else CCList.drop n l in
            let l = List.map (mono_term ~state ~local_state) l in
            U.app (U.const new_id) l
        | TI.Var v ->
            (* allow variables in head (in spec/rec and in functions) *)
            begin match Subst.find ~subst:local_state.subst v with
            | None ->
                let v = mono_var ~state ~local_state v in
                let l = List.map (mono_term ~state ~local_state) l in
                U.app (U.var v) l
            | Some t ->
                mono_term ~state ~local_state (U.app t l)
            end
        | _ ->
            failf_ "@[<2>cannot monomorphize application term@ `@[%a@]`@]" print_term t
        end
    | TI.Bind ((`Fun | `Forall | `Exists) as b, v, t) ->
        U.mk_bind b
          (mono_var ~state ~local_state v)
          (mono_term ~state ~local_state t)
    | TI.Let (v,t,u) ->
        U.let_ (mono_var ~state ~local_state v)
          (mono_term ~state ~local_state t)
          (mono_term ~state ~local_state u)
    | TI.Match (t,l) ->
        let t = mono_term ~state ~local_state t in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let vars = List.map (mono_var ~state ~local_state) vars in
            vars, mono_term ~state ~local_state rhs
          ) l
        in
        U.match_with t l
    | TI.TyBuiltin b -> U.ty_builtin b
    | TI.TyArrow (a,b) ->
        U.ty_arrow
          (mono_term ~state ~local_state a)
          (mono_term ~state ~local_state b)
    | TI.TyMeta _ -> assert false
    | TI.Bind (`TyForall,_,_) ->
        failf_ "cannot monomorphize quantified type %a" print_ty t

  and mono_var ~state ~local_state v : term Var.t =
    Var.update_ty v ~f:(mono_type ~state ~local_state)

  and mono_type ~state ~local_state t : term =
    mono_term ~state ~local_state t

  (* take [n] ground atomic type arguments in [l], or fail *)
  and take_n_ground_atomic_types_ ~state ~local_state n = function
    | _ when n=0 -> []
    | [] -> failf_ "not enough arguments (%d missing)" n
    | t :: l' ->
        U.eval ~subst:local_state.subst t
        :: take_n_ground_atomic_types_ ~state ~local_state (n-1) l'

  (* use the generic traversal *)
  module Trav = Traversal.Make(T)(struct
    type t = ArgTuple.t
    let equal = ArgTuple.equal
    let hash _ = 0
    let print = ArgTuple.print
    let section = section
    let fail = failf_
  end)

  let mono_defined ~state ~local_state d tup =
    let ty = U.ty_apply d.Stmt.defined_ty (ArgTuple.m_args tup) in
    let defined_ty = mono_type ~state ~local_state ty in
    let defined_head, _ = mangle_ ~state d.Stmt.defined_head (ArgTuple.m_args tup) in
    {Stmt.defined_head; defined_ty; }

  (* monomorphize equations properly
     n: number of type arguments *)
  let mono_eqns
  : type a b.
      state:_ St.t -> local_state:local_state -> int ->
      (_,_,(a,b) inv1) Stmt.equations -> (_,_,(a,b) inv2) Stmt.equations
  = fun ~state ~local_state n eqn ->
    let f e = Stmt.map_eqns e
      ~term:(mono_term ~state ~local_state)
      ~ty:(mono_type ~state ~local_state)
    in
    match eqn with
      | Stmt.Eqn_linear l ->
          f (Stmt.Eqn_linear
            (List.map
              (fun (vars, rhs, side) -> CCList.drop n vars, rhs, side)
              l))
      | Stmt.Eqn_nested l ->
          f (Stmt.Eqn_nested
            (List.map
              (fun (vars, args, rhs, side) -> vars, CCList.drop n args, rhs, side)
              l))
      | Stmt.Eqn_single (vars, rhs) ->
          let vars = CCList.drop n vars in
          Stmt.Eqn_single (vars, mono_term ~state ~local_state rhs)

  let conf = {Traversal.
    direct_tydef=false;
    direct_spec=false;
    direct_mutual_types=false;
  }

  class ['inv1, 'inv2, 'c] mono_traverse ?size ?depth_limit () = object (self)
    inherit ['inv1, 'inv2, 'c] Trav.traverse ~conf ?size ?depth_limit ()

    val st : (_, _) St.t = St.create ()

    method setup =
      st.St.fun_ <- self#do_statements_for_id;
      st.St.get_env <- (fun () -> self#env);
      ()

    method decode_state = st.St.unmangle

    method do_term ~depth t =
      mono_term ~state:st ~local_state:{subst=Subst.empty; depth;} t

    (* specialize mutual recursive definitions *)
    method do_def ~depth def arg =
      Utils.debugf ~section 5 "monomorphize def %a on %a"
        (fun k->k ID.print def.Stmt.rec_defined.Stmt.defined_head ArgTuple.print arg);
      let subst = match_rec ~def arg in
      (* we know [subst case.defined = (id args)], now
          specialize the axioms and other fields *)
      let local_state = {subst; depth=depth+1; } in
      let n = List.length def.Stmt.rec_vars in
      let eqns = mono_eqns ~state:st ~local_state n def.Stmt.rec_eqns in
      (* new (specialized) case *)
      let rec_defined = mono_defined ~state:st ~local_state def.Stmt.rec_defined arg in
      let def' = {Stmt.
        rec_kind=def.Stmt.rec_kind;
        rec_vars=[];
        rec_defined;
        rec_eqns=eqns;
      } in
      [def']

    method do_pred ~depth def arg =
      Utils.debugf ~section 5 "monomorphize pred %a on %a"
        (fun k->k ID.print def.Stmt.pred_defined.Stmt.defined_head ArgTuple.print arg);
      let subst = match_pred ~def arg in
      (* we know [subst case.defined = (id args)], now
          specialize the axioms and other fields *)
      let local_state = {subst; depth=depth+1; } in
      let clauses =
        List.map
          (Stmt.map_clause
          ~term:(mono_term ~state:st ~local_state)
          ~ty:(mono_term ~state:st ~local_state))
        def.Stmt.pred_clauses
      in
      (* new (specialized) case *)
      let pred_defined = mono_defined ~state:st ~local_state
        def.Stmt.pred_defined arg in
      let def' = {Stmt.
        pred_tyvars=[];
        pred_defined;
        pred_clauses=clauses;
      } in
      [def']

    (* declare a symbol that is axiomatized *)
    method decl_sym id tup =
      if not (self#has_declared id tup) then (
        let env_info = Env.find_exn ~env:self#env id in
        (* declare specialized type *)
        let new_id = match ArgTuple.mangled tup with
          | None -> id
          | Some x -> x
        in
        let ty = U.ty_apply env_info.Env.ty (ArgTuple.args tup) in
        let new_ty = mono_type ~state:st ~local_state:{depth=0; subst=Subst.empty} ty in
        self#declare_sym id tup ~as_:new_id ~ty:new_ty
      )

    (* specialize specification *)
    method do_spec ~depth ~loc id spec tup =
      Utils.debugf ~section 5 "monomorphize spec for %a on %a"
        (fun k->k ID.print id ArgTuple.print tup);
      assert (ArgTuple.length tup = List.length spec.Stmt.spec_vars);
      if not (self#has_processed id tup) then (
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
            self#done_processing id' tup';
          )
          spec.Stmt.spec_defined;
        (* convert axioms and defined terms *)
        let defined = List.map
          (fun d -> mono_defined ~state:st ~local_state:{depth; subst;} d tup)
          spec.Stmt.spec_defined
        and axioms = List.map
          (fun ax -> mono_term ~state:st ~local_state:{depth; subst; } ax)
          spec.Stmt.spec_axioms
        in
        let st' = Stmt.axiom_spec ~info:{Stmt.loc; name=None}
          {Stmt.spec_axioms=axioms; spec_defined=defined; spec_vars=[]; }
        in
        self#push_res st';
      );
      ()

    method do_mutual_types ~depth tydef tup =
      Utils.debugf ~section 5 "monomorphize data %a on %a"
        (fun k->k ID.print tydef.Stmt.ty_id ArgTuple.print tup);
      (* mangle type name. Monomorphized type should be : Type *)
      let id, _ =
        mangle_ ~state:st tydef.Stmt.ty_id (ArgTuple.m_args tup) in
      let ty = U.ty_type in
      (* specialize each constructor *)
      let cstors = ID.Map.fold
        (fun _ c acc ->
          (* mangle ID *)
          let id', _ = mangle_ ~state:st c.Stmt.cstor_name (ArgTuple.m_args tup) in
          (* apply, then convert type. Arity should match. *)
          let ty', subst =
            U.ty_apply_full c.Stmt.cstor_type (ArgTuple.args tup)
          in
          (* convert type and substitute in it *)
          let ty' = mono_term
            ~state:st ~local_state:{depth=0; subst;} ty' in
          let local_state = {depth=depth+1; subst} in
          let args' = List.map (mono_term ~state:st ~local_state) c.Stmt.cstor_args in
          let c' = { Stmt.cstor_name=id'; cstor_type=ty'; cstor_args=args'; } in
          ID.Map.add id' c' acc
        )
        tydef.Stmt.ty_cstors
        ID.Map.empty
      in
      (* add monomorphized type to [res] *)
      let tydef' = {Stmt.
        ty_id=id; ty_type=ty; ty_cstors=cstors; ty_vars=[];
      } in
      [tydef']

    method do_ty_def ?loc decl id ~ty tup =
      Utils.debugf ~section 5 "declare type for %a on %a"
        (fun k->k ID.print id ArgTuple.print tup);
      begin match decl with
      | Stmt.Decl_type ->
          (* type declaration must be done only once
             (St.is_already_specialized is not precise enough, because
             here we must ignore [tup]) *)
          if not (self#has_declared id ArgTuple.empty) then (
            self#done_declaring id ArgTuple.empty;
            let new_ty = mono_type ~state:st
              ~local_state:{depth=0; subst=Subst.empty} ty in
            self#push_res
              (Stmt.ty_decl ~info:{Stmt.loc; name=None} id new_ty)
          )
      | Stmt.Decl_fun
      | Stmt.Decl_prop -> self#decl_sym id tup
      end
  end

  (* TODO: gather by ID first *)
  let print_tbl_ out tbl =
    Trav.IDArgTbl.to_seq tbl
    |> Sequence.map fst
    |> Format.fprintf out "@[<v>%a@]"
        (CCFormat.seq ~start:"" ~stop:"" ~sep:""
          (fun out (id,tup) ->
            Format.fprintf out "@[<h>%a (%a)@]" ID.print id ArgTuple.print tup))

  let monomorphize ?(depth_limit=256) pb =
    (* create the state used for monomorphization. Toplevel function
      for specializing (id,tup) is [mono_statements_for_id] *)
    let traverse = new mono_traverse ~depth_limit () in
    traverse#setup;
    (* iterate on statements *)
    CCVector.iter
      (fun st -> traverse#do_stmt st)
      (Problem.statements pb);
    (* output result. If depth limit reached we might be incomplete *)
    let meta = Problem.metadata pb in
    let meta =
      Problem.Metadata.add_incomplete meta traverse#reached_depth_limit in
    let res = traverse#output in
    let pb' = Problem.make ~meta (CCVector.freeze res) in
    (* some debug *)
    Utils.debugf ~section 3 "@[<2>instances:@ @[%a@]@]"
      (fun k-> k print_tbl_ traverse#processed);
    pb', traverse#decode_state

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
      | TI.Bind ((`Forall | `Exists | `Fun) as b,v,t) ->
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
    Model.map ~f:(unmangle_term ~state)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after mono: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name:"monomorphization"
      ~encode:(fun p ->
        let p, state = monomorphize p in
        p, state
        (* TODO mangling of types, as an option *)
      )
      ~decode
      ()

  let pipe ~print =
    let decode state = Model.map ~f:(unmangle_term ~state) in
    pipe_with ~print ~decode
end
