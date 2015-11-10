
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module TyI = NunType_intf
module Stmt = NunStatement
module Env = NunEnv
module Callback = NunUtils.Callback

type id = ID.t

let section = NunUtils.Section.make "mono"

type inv1 = <meta:[`NoMeta]; poly:[`Poly]>
type inv2 = <meta:[`NoMeta]; poly:[`Mono]>

module Make(T : NunTerm_ho.S) = struct
  module T = T

  type term1 = inv1 T.t
  type term2 = inv2 T.t

  module U = NunTerm_ho.Util(T)

  (* substitution *)
  module Subst = Var.Subst
  module SubstUtil = NunTerm_ho.SubstUtil(T)
  module Red = NunReduce.Make(T)

  exception InvalidProblem of string

  let print_ty out t = NunTerm_ho.print_ty ~repr:T.repr out t
  let print_term out t = NunTerm_ho.print ~repr:T.repr out t

  let () = Printexc.register_printer
    (function
      | InvalidProblem msg -> Some ("monomorphization: invalid problem: " ^ msg)
      | _ -> None
    )

  let fpf = Format.fprintf

  let fail_ msg = raise (InvalidProblem msg)
  let failf_ msg =
    NunUtils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidProblem msg))

  (* A tuple of arguments that a given function symbol should be
     instantiated with *)
  module ArgTuple = struct
    type t = {
      args: term1 list; (** Type arguments, before being processed *)
      m_args: term2 list; (** Type arguments, processed (and possibly mangled) *)
      mangled: ID.t option; (* mangled name of [f args] *)
    }

    let empty = {args=[]; m_args=[]; mangled=None;}
    let make ~mangled ~args ~m_args = {mangled; args; m_args; }
    let args t = t.args
    let m_args t = t.m_args
    let mangled t = t.mangled

    (* equality for ground atomic types T.t *)
    let rec ty_ground_eq_
    : term1 -> term1 -> bool
    = fun t1 t2 -> match U.as_ty t1, U.as_ty t2 with
      | TyI.Var _,_
      | TyI.Forall (_,_),_ -> failf_ "type `@[%a@]` is not ground" print_ty t1
      | _, TyI.Var _
      | _, TyI.Forall (_,_) -> failf_ "type `@[%a@]` is not ground" print_ty t2
      | TyI.Builtin b1, TyI.Builtin b2 -> NunBuiltin.Ty.equal b1 b2
      | TyI.Const id1, TyI.Const id2 -> ID.equal id1 id2
      | TyI.App (f1,l1), TyI.App (f2,l2) ->
          ty_ground_eq_ f1 f2 && CCList.equal ty_ground_eq_ l1 l2
      | TyI.Arrow (a1,b1), TyI.Arrow (a2,b2) ->
          ty_ground_eq_ a1 a2 && ty_ground_eq_ b1 b2
      | TyI.Const _, _
      | TyI.App _, _
      | TyI.Builtin _, _
      | TyI.Arrow _, _ -> false

    let equal tup1 tup2 =
      CCList.equal ty_ground_eq_ tup1.args tup2.args

    let print out tup =
      let pp_mangled out = function
        | None -> ()
        | Some id -> fpf out " as %a" ID.print_name id
      in
      fpf out "@[%a%a@]"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:", " print_ty) tup.args
        pp_mangled tup.mangled
  end

  module ArgTupleSet = struct
    type t = ArgTuple.t list

    let empty = []

    let rec mem tup = function
      | [] -> false
      | tup' :: l' -> ArgTuple.equal tup tup' || mem tup l'

    (* add [tup] to the set [l] *)
    let add tup l =
      if mem tup l then l else tup :: l

    let print out =
      fpf out "@[<hv>%a@]" (CCFormat.list ~start:"" ~stop:"" ArgTuple.print)
  end

  (** set of tuples of parameters to instantiate a given function symbol with *)
  module SetOfInstances = struct
    type t = ArgTupleSet.t ID.Tbl.t (* function -> set of args *)

    let create() = ID.Tbl.create 32

    let args t id = match ID.Tbl.get t id with
      | None -> ArgTupleSet.empty
      | Some s -> s

    let mem t id tup = ArgTupleSet.mem tup (args t id)

    let add t id tup =
      let set = args t id in
      let set = ArgTupleSet.add tup set in
      (* add a tuple of args for [id], and require [id] *)
      ID.Tbl.replace t id set

    let print out t =
      let pp_pair out (a,b) =
        fpf out "@[<h>%a -> %a@]" ID.print_name a ArgTupleSet.print b
      in
      fpf out "{@[<hv>%a@]@,}"
        (CCFormat.seq ~start:"" ~stop:"" pp_pair) (ID.Tbl.to_seq t)
  end

  let find_ty_ ~env id =
    try Env.find_ty_exn ~env id
    with Not_found ->
      fail_ ("symbol " ^ ID.to_string id ^ " is not declared")

  (** Configuration for the monomorphization phase *)
  type config = {
    max_depth: int;
  }

  type unmangle_state = (ID.t * term2 list) ID.Tbl.t
  (* used for unmangling *)

  module St = struct
    type depth = int

    type 'inv t = {
      mutable env: (term1, term1, 'inv) Env.t;
        (* access definitions/declarations by ID *)
      config: config;
        (* settings *)
      output: (term2, term2, 'inv) Stmt.t CCVector.vector;
        (* statements that have been specialized *)
      mutable depth_reached: bool;
        (* was [max_depth] reached? *)
      mangle : (string, ID.t) Hashtbl.t;
        (* mangled name -> mangled ID *)
      unmangle : unmangle_state;
        (* mangled name -> (id, args) *)
      already_specialized: SetOfInstances.t;
        (* tuples already instantiated *)
      already_declared: SetOfInstances.t;
        (* symbols already declared *)
      specialize: (state:'inv t -> depth:depth -> ID.t -> ArgTuple.t -> unit) Stack.t;
        (* stack of functions used to specialize a [id, tup] *)
    }

    let is_already_specialized ~state id tup =
      SetOfInstances.mem state.already_specialized id tup

    let create ~config ~env ~specialize () = {
      env;
      config;
      output=CCVector.create ();
      depth_reached=false;
      already_specialized=SetOfInstances.create();
      already_declared=SetOfInstances.create();
      mangle=Hashtbl.create 64;
      unmangle=ID.Tbl.create 64;
      specialize=(
        let st = Stack.create () in
        Stack.push specialize st;
        st
      );
    }

    let depth_limit ~state = state.config.max_depth

    let check_depth ~state d =
      if d>depth_limit ~state && not state.depth_reached then (
        NunUtils.debugf ~section 1 "caution: depth limit reached" (fun k -> k);
        state.depth_reached <- true;
      )

    (* remember that (id,tup) -> mangled *)

    let save_mangled ~state id tup ~mangled =
      try Hashtbl.find state.mangle mangled
      with Not_found ->
        (* create new ID *)
        let mangled' = ID.make ~name:mangled in
        Hashtbl.add state.mangle mangled mangled';
        ID.Tbl.replace state.unmangle mangled' (id, tup);
        mangled'

    (* add dependency on [id] applied to [tup] *)
    let specialization_is_done ~state id tup =
      SetOfInstances.add state.already_specialized id tup

    let declaration_is_done ~state id tup =
      SetOfInstances.add state.already_declared id tup

    let is_already_declared ~state id tup =
      SetOfInstances.mem state.already_declared id tup

    let current_specialize ~state =
      try Stack.top state.specialize
      with Stack.Empty ->
        failf_ "stack of specialize function is empty"

    let push_specialize ~state f = Stack.push f state.specialize

    let pop_specialize ~state = let _ = Stack.pop state.specialize in ()

    (* specialize [id, tup] using the topmost element of [state.specialize]. *)
    let specialize ~state ~depth id tup =
      if not (is_already_specialized ~state id tup)
      && not (is_already_declared ~state id tup)
        then NunUtils.debugf ~section 3 "specialize %a on %a"
          (fun k-> k ID.print_name id ArgTuple.print tup);
      let f = current_specialize ~state in
      f ~state ~depth id tup

    (* output statement *)
    let push_res ~state st = CCVector.push state.output st
  end

  (* find a specialized name for [id tup] if [tup] not empty.
     returns ID to use, and [Some mangled] if [args <> []], None otherwise
     (so it can be used in [!ArgTuple.of_list ~mangled]).
     @param args already mangled arguments *)
  let mangle_ ~state id (args:term2 list) =
    let pp_list p = CCFormat.list ~start:"" ~stop:"" ~sep:"_" p in
    let rec flat_ty_ out (t:term2) = match U.as_ty t with
      | TyI.Builtin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
      | TyI.Const id -> ID.print_name out id
      | TyI.App (f,l) ->
          fpf out "%a_%a" flat_ty_ f (pp_list flat_ty_) l
      | TyI.Arrow (a,b) -> fpf out "%a_to_%a" flat_ty_ a flat_ty_ b
    in
    match args with
    | [] -> id, None
    | _::_ ->
      let name = CCFormat.sprintf "@[<h>%a@]" flat_ty_ (U.app (U.const id) args) in
      let mangled = St.save_mangled ~state id args ~mangled:name in
      mangled, Some mangled

  (* should [id] be mangled? in all cases, yes, except if it's an
     uninterpreted type. *)
  let should_be_mangled_ ~state id =
    match Env.find_exn ~env:state.St.env id with
    | {Env.def=(Env.Fun _ | Env.Cstor _ | Env.Data _); _} ->
        true (* defined objects: mangle *)
    | {Env.def=Env.NoDef; decl_kind=(Stmt.Decl_fun | Stmt.Decl_prop); _} ->
        true (* functions and prop: mangle *)
    | {Env.def=Env.NoDef; decl_kind=Stmt.Decl_type; _} ->
        false (* uninterpreted poly types: do not mangle *)

  (* does this rec_def match [id tup]? If yes, return [def, subst] *)
  let match_rec ?(subst=Subst.empty) ~def id tup =
    let t = U.app (U.const id) (ArgTuple.args tup) in
    CCOpt.map
      (fun subst -> def, subst)
      (SubstUtil.match_ ~subst2:subst def.Stmt.rec_defined.Stmt.defined_term t)

  (* find a definition matching [id tup] in [cases], or None *)
  let find_def ?subst ~defs id tup =
    CCList.find_map
      (fun def ->
        CCOpt.map
          (fun (def,subst) -> defs, def, subst)
          (match_rec ?subst ~def id tup)
      )
      defs

  (* does this spec match [id tup]? If yes, return [spec, subst] *)
  let match_spec ?(subst=Subst.empty) ~spec id tup =
    let t = U.app (U.const id) (ArgTuple.args tup) in
    CCList.find
      (fun defined -> SubstUtil.match_ ~subst2:subst defined.Stmt.defined_term t)
      spec.Stmt.spec_defined

  (* find a (co)inductive type declaration for [id] *)
  let find_tydef_ ~defs id =
    CCList.find_pred
      (fun tydef -> ID.equal id tydef.Stmt.ty_id)
      defs

  (* local state for monomorphization, used in recursive traversal of terms *)
  type local_state = {
    depth: int;
    subst: (term1,term1) Subst.t;
  }

  (* monomorphize term *)
  let rec mono_term ~state ~local_state (t:term1) : term2 =
    match T.repr t with
    | TI.AppBuiltin (b,l) ->
        U.app_builtin b (List.map (mono_term ~state ~local_state) l)
    | TI.Const c ->
        (* no args, but we require [c, ()] in the output *)
        let depth = local_state.depth+1 in
        St.specialize ~state ~depth c ArgTuple.empty;
        U.const c
    | TI.TyVar v ->
        begin match Subst.find ~subst:local_state.subst v with
        | Some t' -> mono_term ~state ~local_state t'
        | None ->
            failf_ "type variable %a not bound" Var.print v
        end
    | TI.Var v ->
        assert (not (Subst.mem ~subst:local_state.subst v));
        U.var (mono_var ~state ~local_state v)
    | TI.App (f,l) ->
        (* first, beta-reduce locally; can possibly enrich [subst] *)
        let f, l, subst = Red.Full.whnf ~subst:local_state.subst f l in
        let local_state = {local_state with subst; } in
        begin match T.repr f with
        | TI.Bind (TI.Fun, _, _) -> assert false (* beta-reduction failed? *)
        | TI.AppBuiltin _ ->
            (* builtins are defined, but examine their args *)
            let f = mono_term ~state ~local_state f in
            let l = List.map (mono_term ~state ~local_state) l in
            U.app f l
        | TI.Const id ->
            (* find type arguments *)
            let ty = find_ty_ ~env:state.St.env id in
            let n = TyI.num_param ~repr:U.as_ty ty in
            (* tuple of arguments for [id], not encoded yet *)
            let unmangled_tup = take_n_ground_atomic_types_ ~state ~local_state n l in
            let mangled_tup = List.map (mono_type ~state ~local_state) unmangled_tup in
            (* mangle? *)
            let new_id, mangled =
              if should_be_mangled_ ~state id then mangle_ ~state id mangled_tup
              else id, None
            in
            (* specialize [id] *)
            let unmangled_tup = ArgTuple.make
              ~mangled ~args:unmangled_tup ~m_args:mangled_tup in
            let depth = local_state.depth + 1 in
            St.specialize ~state ~depth id unmangled_tup;
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
    | TI.Bind ((TI.Fun | TI.Forall | TI.Exists) as b, v, t) ->
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
    | TI.Bind (TI.TyForall,_,_) ->
        failf_ "cannot monomorphize quantified type %a" print_ty t

  (* monomorphize a variable (rather, its type) *)
  and mono_var ~state ~local_state v : term2 Var.t =
    Var.update_ty v ~f:(mono_type ~state ~local_state)

  and mono_type ~state ~local_state t : term2 =
    mono_term ~state ~local_state t

  (* take [n] ground atomic type arguments in [l], or fail *)
  and take_n_ground_atomic_types_ ~state ~local_state n = function
    | _ when n=0 -> []
    | [] -> failf_ "not enough arguments (%d missing)" n
    | t :: l' ->
        SubstUtil.eval ~subst:local_state.subst t
        :: take_n_ground_atomic_types_ ~state ~local_state (n-1) l'

  (* declare a symbol that is axiomatized *)
  and decl_sym ~state id tup =
    if not (St.is_already_declared ~state id tup) then (
      (* only declare once *)
      St.declaration_is_done ~state id tup;
      let env_info = Env.find_exn ~env:state.St.env id in
      let loc = env_info.Env.loc in
      (* declare specialized type *)
      let new_id = match ArgTuple.mangled tup with
        | None -> id
        | Some x -> x
      in
      let ty = SubstUtil.ty_apply env_info.Env.ty (ArgTuple.args tup) in
      let new_ty = mono_type ~state ~local_state:{depth=0; subst=Subst.empty} ty in
      St.push_res ~state
        (Stmt.mk_decl ~info:{Stmt.loc; name=None}
          new_id env_info.Env.decl_kind new_ty);
    )

  let mono_defined ~state ~local_state d =
    let defined_term = mono_term ~state ~local_state d.Stmt.defined_term in
    let defined_ty_args =
      List.map (mono_type ~state ~local_state) d.Stmt.defined_ty_args in
    let defined_head = TI.head_sym ~repr:T.repr defined_term in
    {Stmt. defined_term; defined_head; defined_ty_args; }

  (* specialize mutual recursive definitions *)
  let mono_rec_defs ~state ~depth (defs, def, loc) tup =
    let q = Queue.create () in (* task list, for the fixpoint *)
    let res = ref [] in (* resulting axioms *)
    (* if we required monomorphization of [id tup], and some case in [l]
       matches [id tup], then push into the queue so that it will be
       processed in the fixpoint. Otherwise, [id] must be declared/defined
       earlier and must be processed before we are done with [defs] *)
    let specialize' = St.current_specialize ~state in
    St.push_specialize ~state
      (fun ~state ~depth id tup ->
        match find_def ~defs id tup with
        | None ->
            (* delegate to previous specialization function *)
            specialize' ~state ~depth id tup
        | Some (_cases, def, subst) ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, def, subst) q
      );
    (* push first tuple in queue *)
    begin match match_rec ~def def.Stmt.rec_defined.Stmt.defined_head tup with
      | None -> ()  (* definition does not match, do nothing *)
      | Some (def, subst) ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, def, subst) q
    end;
    (* fixpoint *)
    while not (Queue.is_empty q) do
      let tup, depth, def, subst = Queue.take q in
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      (* check for depth limit *)
      St.check_depth ~state depth;
      if depth > St.depth_limit ~state
      || St.is_already_specialized ~state id tup
      then ()
      else (
        NunUtils.debugf ~section 3
          "@[<2>process case `%a` for@ (%a %a)@ at depth %d@]"
          (fun k -> k print_term def.Stmt.rec_defined.Stmt.defined_term
            ID.print_no_id id ArgTuple.print tup depth);
        St.specialization_is_done ~state id tup;
        (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
        let local_state = {subst; depth=depth+1; } in
        let eqns = List.map
          (Stmt.map_eqn
            ~term:(mono_term ~state ~local_state)
            ~ty:(mono_type ~state ~local_state)
          )
          def.Stmt.rec_eqns
        in
        (* new (specialized) case *)
        let rec_defined = mono_defined ~state ~local_state def.Stmt.rec_defined in
        let def' = {Stmt.
          rec_vars=[]; (* should be monomorphic now *)
          rec_defined;
          rec_eqns=eqns;
        } in
        (* declare the symbol *)
        decl_sym ~state id tup;
        (* push new case to the list *)
        CCList.Ref.push res def';
      )
    done;
    (* remove callback *)
    St.pop_specialize ~state;
    (* push result, if any *)
    if !res <> []
    then
      let stmt = Stmt.axiom_rec ~info:{Stmt.name=None; loc;} !res in
      St.push_res ~state stmt;
    ()

  (* specialize specification *)
  let mono_spec ~state ~depth (spec,loc) id tup =
    (* compute subst for the defined term that matches [id tup]... if any *)
    match match_spec ~spec id tup with
    | Some subst when not (St.is_already_specialized ~state id tup) ->
      (* flag every symbol as specialized. Careful, tup changes from term
        to term (e.g. [@f (list a)] and [@g (array a)]), even though
        the set of type variables involved is always the same by invariant. *)
      List.iter
        (fun d ->
          let id' = d.Stmt.defined_head in
          let tup' = List.map (SubstUtil.eval ~subst) d.Stmt.defined_ty_args in
          let mangled_tup' = List.map
            (mono_type ~state ~local_state:{subst;depth}) tup'
          in
          let _, mangled = mangle_ ~state id' mangled_tup' in
          let tup' = ArgTuple.make ~mangled ~args:tup' ~m_args:mangled_tup' in
          decl_sym ~state id' tup';
          NunUtils.debugf ~section 4 "specialization of %a %a is done"
            (fun k -> k ID.print_name id' ArgTuple.print tup');
          St.specialization_is_done ~state id' tup'
        )
        spec.Stmt.spec_defined;
      (* convert axioms and defined terms *)
      let defined = List.map
        (fun d -> mono_defined ~state ~local_state:{depth; subst;} d)
        spec.Stmt.spec_defined
      and axioms = List.map
        (fun ax -> mono_term ~state ~local_state:{depth; subst; } ax)
        spec.Stmt.spec_axioms
      in
      let st' = Stmt.axiom_spec ~info:{Stmt.loc; name=None}
        {Stmt.spec_axioms=axioms; spec_defined=defined; spec_vars=[]; }
      in
      St.push_res ~state st';
      ()
    | Some _
    | None -> ()

  (* specialize (co)inductive types *)
  let mono_mutual_types ~state ~depth ~kind tydefs tydef tup loc =
    let tydefs = ref tydefs in
    let q = Queue.create() in (* task list *)
    let res = ref [] in
    (* whenever a type [id tup] is needed, check if it's in the block *)
    let specialize' = St.current_specialize ~state in
    St.push_specialize ~state
      (fun ~state ~depth id tup ->
        match find_tydef_ ~defs:!tydefs id with
        | None ->
            begin match Env.find ~env:state.St.env id with
            | Some {Env.def=Env.Data (kind', tydefs', tydef'); _} ->
                (* make id and current type mutual, even though they were not *)
                if kind <> kind'
                  then failf_
                    "@[<2>cannot handle nested {(co)data, data}:@ @[<h>{%a, %a}@]@]"
                    ID.print_name id ID.print_name tydef.Stmt.ty_id;
                tydefs := tydefs' @ !tydefs; (* bigger recursive block! *)
                Queue.push (tydef', depth, tup) q
            | _ ->
                (* not in this block, use the previous specialization fun *)
                NunUtils.debugf ~section 4
                  "%a not in same block, fallback to previous specialize function"
                  (fun k -> k ID.print_name id);
                specialize' ~state ~depth id tup
            end
        | Some tydef ->
            (* specialize in the same block of mutual types *)
            NunUtils.debugf ~section 4
              "%a in same block, specialize in same (co)data"
              (fun k -> k ID.print_name id);
            Queue.push (tydef, depth, tup) q
      );
    (* initialization: push the first tuple to process *)
    Queue.push (tydef, depth, tup) q;
    (* fixpoint *)
    while not (Queue.is_empty q) do
      let tydef, depth, tup = Queue.pop q in
      (* check for depth limit *)
      St.check_depth ~state depth;
      if depth > St.depth_limit ~state
      || St.is_already_specialized ~state tydef.Stmt.ty_id tup
      then ()
      else (
        NunUtils.debugf ~section 3
          "@[<2>process type decl `%a : %a` for@ %a@ at depth %d@]"
          (fun k-> k ID.print_no_id tydef.Stmt.ty_id
          print_ty tydef.Stmt.ty_type ArgTuple.print tup depth);
        St.specialization_is_done ~state tydef.Stmt.ty_id tup;
        (* mangle type name. Monomorphized type should be : Type *)
        let id, _ =
          mangle_ ~state tydef.Stmt.ty_id (ArgTuple.m_args tup) in
        let ty = U.ty_type() in
        (* specialize each constructor *)
        let cstors = List.map
          (fun c ->
            (* mangle ID *)
            let id', _ = mangle_ ~state c.Stmt.cstor_name (ArgTuple.m_args tup) in
            (* apply, then convert type. Arity should match. *)
            let ty', subst =
              SubstUtil.ty_apply_full c.Stmt.cstor_type (ArgTuple.args tup)
            in
            (* convert type and substitute in it *)
            let ty' = mono_term
              ~state ~local_state:{depth=0; subst;} ty' in
            let local_state = {depth=depth+1; subst} in
            let args' = List.map (mono_term ~state ~local_state) c.Stmt.cstor_args in
            { Stmt.cstor_name=id'; cstor_type=ty'; cstor_args=args';  }
          )
          tydef.Stmt.ty_cstors
        in
        (* add monomorphized type to [res] *)
        let tydef' = {Stmt.
          ty_id=id; ty_type=ty; ty_cstors=cstors; ty_vars=[];
        } in
        CCList.Ref.push res tydef'
      )
    done;
    (* cleanup *)
    St.pop_specialize ~state;
    if !res <> [] then (
      let stmt = Stmt.mk_ty_def ~info:{Stmt.name=None; loc} kind !res in
      St.push_res ~state stmt;
    );
    ()

  (* monomorphize every statement that declares or defines [id] *)
  let mono_statements_for_id ~state ~depth id tup =
    let env_info = match Env.find ~env:state.St.env id with
      | None -> failf_ "could not find definition of %a" ID.print_name id
      | Some i -> i
    in
    let loc = Env.loc env_info in
    match Env.def env_info with
    | Env.Fun defs ->
        (* specialize each definition *)
        List.iter
          (function
            | Env.Rec (defs, def, loc) ->
                mono_rec_defs ~state ~depth (defs, def, loc) tup
            | Env.Spec (spec, loc) ->
                mono_spec ~state ~depth (spec,loc) id tup
          )
          defs;
        (* if not definition matched, still need to declare [id_tup] *)
        if not (St.is_already_specialized ~state id tup)
          then decl_sym ~state id tup;
        St.specialization_is_done ~state id tup
    | Env.Data (k,tydefs,tydef) ->
        mono_mutual_types ~state ~depth ~kind:k tydefs tydef tup loc
    | Env.Cstor (k,tydefs,tydef,_cstor) ->
        (* specialize constructor means specializing the whole type *)
        mono_mutual_types ~state ~depth ~kind:k tydefs tydef tup loc
    | Env.NoDef ->
        let ty = env_info.Env.ty in
        begin match env_info.Env.decl_kind with
        | Stmt.Decl_type ->
            (* type declaration must be done only once
               (St.is_already_specialized is not precise enough, because
               here we must ignore [tup]) *)
            if not (St.is_already_declared ~state id ArgTuple.empty) then (
              St.declaration_is_done ~state id ArgTuple.empty;
              let new_ty = mono_type ~state
                ~local_state:{depth=0; subst=Subst.empty} ty in
              St.push_res ~state
                (Stmt.ty_decl ~info:{Stmt.loc; name=None} id new_ty)
            )
        | Stmt.Decl_fun
        | Stmt.Decl_prop ->
            decl_sym ~state id tup;
            (* avoid repeating this declaration *)
            St.specialization_is_done ~state id tup
        end

  (* register the statement into the state's [env], so that next statements
    can monomorphize it. Some statements are automatically kept (goal and axiom) *)
  let mono_statement ~state st =
    NunUtils.debugf ~section 2 "@[<2>enter statement@ `%a`@]"
      (fun k-> k (NunStatement.print print_term print_ty) st);
    (* process statement *)
    let info = Stmt.info st in
    let loc = Stmt.loc st in
    begin match Stmt.view st with
    | Stmt.Decl (id,k,ty) ->
        (* declare the statement (in case it is needed later) *)
        state.St.env <- Env.declare ?loc ~kind:k ~env:state.St.env id ty
    | Stmt.Goal g ->
        (* convert goal *)
        let g = mono_term ~state
          ~local_state:{subst=Subst.empty; depth=0; } g
        in
        St.push_res ~state (Stmt.goal ~info g)
    | Stmt.Axiom (Stmt.Axiom_std l) ->
        (* keep axioms *)
        let local_state={depth=0; subst=Subst.empty} in
        let l = List.map (mono_term ~state ~local_state) l in
        St.push_res ~state (Stmt.axiom ~info l)
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
        state.St.env <- Env.spec_funs ?loc ~env:state.St.env l;
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        state.St.env <- Env.rec_funs ?loc ~env:state.St.env l;
    | Stmt.TyDef (k, l) ->
        state.St.env <- Env.def_data ?loc ~kind:k ~env:state.St.env l;
    end

  let monomorphize ?(depth_limit=256) pb =
    (* create the state used for monomorphization. Toplevel function
      for specializing (id,tup) is [mono_statements_for_id] *)
    let config = {
      max_depth=depth_limit;
    } in
    let env = Env.create () in
    let state = St.create ~config ~env ~specialize:mono_statements_for_id () in
    (* iterate on statements *)
    CCVector.iter
      (fun st -> mono_statement ~state st)
      (NunProblem.statements pb);
    (* output result. If depth limit reached we might be incomplete *)
    let meta = NunProblem.metadata pb in
    let meta = NunProblem.Metadata.add_incomplete meta state.St.depth_reached in
    let pb' = NunProblem.make ~meta (CCVector.freeze state.St.output) in
    (* some debug *)
    NunUtils.debugf ~section 3 "@[<2>instances:@ @[%a@]@]"
      (fun k-> k SetOfInstances.print state.St.already_specialized);
    pb', state.St.unmangle

  let unmangle_term ~(state:unmangle_state) (t:term2):term1 =
    let rec aux (t:term2):term1 = match T.repr t with
      | TI.Var v -> U.var (aux_var v)
      | TI.Const id ->
          begin try
            let id', args = ID.Tbl.find state id in
            U.app (U.const id') (List.map aux args)
          with Not_found -> U.const id
          end
      | TI.App (f,l) -> U.app (aux f) (List.map aux l)
      | TI.AppBuiltin (b,l) -> U.app_builtin b (List.map aux l)
      | TI.Bind ((TI.Forall | TI.Exists | TI.Fun) as b,v,t) ->
          U.mk_bind b (aux_var v) (aux t)
      | TI.Let (v,t,u) -> U.let_ (aux_var v) (aux t) (aux u)
      | TI.Match (t,l) ->
          let t = aux t in
          let l = ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, aux rhs) l in
          U.match_with t l
      | TI.TyBuiltin b -> U.ty_builtin b
      | TI.TyArrow (a,b) -> U.ty_arrow (aux a) (aux b)
    and aux_var = Var.update_ty ~f:aux in
    aux t

  (* rewrite mangled constants to their definition *)
  let unmangle_model ~state =
    NunModel.map ~f:(unmangle_term ~state)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module THO = NunTerm_ho in
        let funs = NunTerm_ho.mk_print ~repr:T.repr in
        [Format.printf "@[<v2>after mono: %a@]@."
          (NunProblem.print
            ~pty_in_app:funs.THO.print_in_app ~pt_in_app:funs.THO.print_in_app
            funs.THO.print funs.THO.print)]
      else []
    in
    NunTransform.make1
      ~on_encoded
      ~name:"monomorphization"
      ~encode:(fun p ->
        let p, state = monomorphize p in
        p, state
        (* TODO mangling of types, as an option *)
      )
      ~decode:(fun state x ->
        let decode_term = unmangle_term ~state in
        decode ~decode_term x
      )
      ()

  let pipe ~print =
    let decode ~decode_term = NunModel.map ~f:decode_term in
    pipe_with ~print ~decode
end
