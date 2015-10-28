
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

module Make(T : NunTerm_ho.S) = struct
  module T = T

  module TyUtils = TyI.Utils(T.Ty)
  module P = NunTerm_ho.Print(T)
  module TU = NunTerm_intf.Util(T)

  (* substitution *)
  module Subst = Var.Subst(struct type t = T.ty end)
  module SubstUtil = NunTerm_ho.SubstUtil(T)(Subst)
  module Red = NunReduce.Make(T)(Subst)

  exception InvalidProblem of string

  let () = Printexc.register_printer
    (function
      | InvalidProblem msg -> Some ("monomorphization: invalid problem: " ^ msg)
      | _ -> None
    )

  let fpf = Format.fprintf

  let fail_ msg = raise (InvalidProblem msg)
  let failf_ msg =
    NunUtils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidProblem msg))

  (* number of parameters of this (polymorphic?) T.ty type *)
  let rec num_param_ty_ ty = match T.Ty.view ty with
    | TyI.Var _
    | TyI.Const _
    | TyI.App _
    | TyI.Builtin _ -> 0
    | TyI.Meta _ -> fail_ "remaining meta-variable"
    | TyI.Arrow (_,t') ->
        if TyUtils.is_Type t'
          then 1 + num_param_ty_ t'
          else 0  (* asks for term parameters *)
    | TyI.Forall (_,t) -> 1 + num_param_ty_ t

  (* A tuple of arguments that a given function symbol should be
     instantiated with *)
  module ArgTuple = struct
    type t = {
      args: T.ty list;
      mangled: ID.t option; (* mangled name of [f args] *)
    }

    let empty = {args=[]; mangled=None;}
    let of_list ~mangled l = {args=l; mangled;}
    let args t = t.args
    let mangled t = t.mangled

    (* equality for ground atomic types T.ty *)
    let rec ty_ground_eq_ t1 t2 = match T.Ty.view t1, T.Ty.view t2 with
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
      | TyI.Var _,_
      | TyI.Meta _,_
      | TyI.Forall (_,_),_ -> failf_ "type @[%a@] is not ground" P.print_ty t1

    let equal tup1 tup2 =
      CCList.equal ty_ground_eq_ tup1.args tup2.args

    let print out tup =
      let pp_mangled out = function
        | None -> ()
        | Some id -> fpf out " as %a" ID.print_name id
      in
      fpf out "@[%a%a@]"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:", " P.print_ty) tup.args
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
      fpf out "@[<hv1>%a@]" (CCFormat.list ~start:"" ~stop:"" ArgTuple.print)
  end

  (** set of tuples of parameters to instantiate a given function symbol with *)
  module SetOfInstances = struct
    type t = ArgTupleSet.t ID.Map.t (* function -> set of args *)

    let empty = ID.Map.empty

    let args t id =
      try ID.Map.find id t
      with Not_found -> ArgTupleSet.empty

    let mem t id tup = ArgTupleSet.mem tup (args t id)

    let add t id tup =
      let set =
        try ID.Map.find id t
        with Not_found -> ArgTupleSet.empty in
      let set = ArgTupleSet.add tup set in
      (* add a tuple of args for [id], and require [id] *)
      ID.Map.add id set t

    let print out t =
      fpf out "{@[<hv>%a@]@,}"
        (ID.Map.print ~start:"" ~stop:"" ID.print_name ArgTupleSet.print) t
  end

  let find_ty_ ~env id =
    try Env.find_ty ~env ~id
    with Not_found ->
      fail_ ("symbol " ^ ID.to_string id ^ " is not declared")

  (** Configuration for the monomorphization phase *)
  type config = {
    max_depth: int;
  }

  type unmangle_state = (ID.t * T.t list) ID.Tbl.t
  (* used for unmangling *)

  module St = struct
    type depth = int

    type t = {
      env: (T.t, T.ty) Env.t;
        (* access definitions/declarations by ID *)
      config: config;
        (* settings *)
      output: (T.t, T.ty) Stmt.t CCVector.vector;
        (* statements that have been specialized *)
      mutable depth_reached: bool;
        (* was [max_depth] reached? *)
      mangle : (string, ID.t) Hashtbl.t;
        (* mangled name -> mangled ID *)
      unmangle : unmangle_state;
        (* mangled name -> (id, args) *)
      mutable already_specialized: SetOfInstances.t;
        (* tuples already instantiated (subset of [required]) *)
      mutable already_declared: SetOfInstances.t;
        (* symbols already declared *)
      specialize: (state:t -> depth:depth -> ID.t -> ArgTuple.t -> unit) Stack.t;
        (* stack of functions used to specialize a [id, tup] *)
    }

    let is_already_specialized ~state id tup =
      SetOfInstances.mem state.already_specialized id tup

    let create ~config ~env ~specialize () = {
      env;
      config;
      output=CCVector.create ();
      depth_reached=false;
      already_specialized=SetOfInstances.empty;
      already_declared=SetOfInstances.empty;
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
      state.already_specialized <-
        SetOfInstances.add state.already_specialized id tup

    let declaration_is_done ~state id tup =
      state.already_declared <- SetOfInstances.add state.already_declared id tup

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
        then NunUtils.debugf ~section 3 "specialize %a on %a"
          (fun k-> k ID.print_name id ArgTuple.print tup);
      (* avoid loops *)
      let f = current_specialize ~state in
      f ~state ~depth id tup

    (* output statement *)
    let push_res ~state st = CCVector.push state.output st
  end

  (* find a specialized name for [id tup] if [tup] not empty.
   returns ID to use, and [Some mangled] if [args <> []], None otherwise
   (so it can be used in [!ArgTuple.of_list ~mangled]) *)
  let mangle_ ~state id args =
    let pp_list p = CCFormat.list ~start:"" ~stop:"" ~sep:"_" p in
    let rec flat_ty_ out t = match T.Ty.view t with
      | TyI.Builtin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
      | TyI.Const id -> ID.print_name out id
      | TyI.Var v ->
          failf_ "@[<2>mangling: cannot mangle variable `%a` in `@[%a (%a)@]`@]"
            Var.print v ID.print_name id (CCFormat.list P.print_ty) args
      | TyI.Meta _ -> assert false
      | TyI.App (f,l) ->
          fpf out "%a_%a" flat_ty_ f (pp_list flat_ty_) l
      | TyI.Arrow (a,b) -> fpf out "%a_to_%a" flat_ty_ a flat_ty_ b
      | TyI.Forall (_,_) -> failf_ "mangling: cannot mangle %a" P.print_ty t
    in
    match args with
    | [] -> id, None
    | _::_ ->
      let name = CCFormat.sprintf "@[<h>%a@]" flat_ty_ (T.app (T.const id) args) in
      let mangled = St.save_mangled ~state id args ~mangled:name in
      mangled, Some mangled

  (* should [id] be mangled? in all cases, yes, except if it's an
     uninterpreted type. *)
  let should_be_mangled_ ~state id =
    match Env.find_exn ~env:state.St.env ~id with
    | {Env.def=(Env.Fun _ | Env.Cstor _ | Env.Data _); _} ->
        true (* defined objects: mangle *)
    | {Env.def=Env.NoDef; decl_kind=(Stmt.Decl_fun | Stmt.Decl_prop); _} ->
        true (* functions and prop: mangle *)
    | {Env.def=Env.NoDef; decl_kind=Stmt.Decl_type; _} ->
        false (* uninterpreted poly types: do not mangle *)

  (* does this case match [id tup]? If yes, return [case, subst] *)
  let match_case ?(subst=Subst.empty) ~case id tup =
    let t = T.app (T.const id) (ArgTuple.args tup) in
    CCOpt.map
      (fun subst -> case, subst)
      (SubstUtil.match_ ~subst2:subst case.Stmt.case_defined t)

  (* find a case matching [id tup] in [cases], or None *)
  let find_case_ ?subst ~cases id tup =
    CCList.find_map
      (fun case ->
        CCOpt.map
          (fun (case,subst) -> cases, case, subst)
          (match_case ?subst ~case id tup)
      )
      cases

  (* find a (co)inductive type declaration for [id] *)
  let find_tydef_ ~defs id =
    CCList.find_pred
      (fun tydef -> ID.equal id tydef.Stmt.ty_id)
      defs

  (* local state for monomorphization, used in recursive traversal of terms *)
  type local_state = {
    depth: int;
    subst: T.ty Subst.t;
  }

  (* monomorphize term *)
  let rec mono_term ~state ~local_state t =
    match T.view t with
    | TI.AppBuiltin (b,l) ->
        T.app_builtin b (List.map (mono_term ~state ~local_state) l)
    | TI.Const c ->
        (* no args, but we require [c, ()] in the output *)
        let depth = local_state.depth+1 in
        St.specialize ~state ~depth c ArgTuple.empty;
        T.const c
    | TI.Var v ->
        begin match Subst.find ~subst:local_state.subst v with
        | Some t' -> mono_term ~state ~local_state t'
        | None ->
            let v = mono_var ~state ~local_state v in
            T.var v
        end
    | TI.App (f,l) ->
        (* first, beta-reduce locally; can possibly enrich [subst] *)
        let f, l, subst = Red.Full.whnf ~subst:local_state.subst f l in
        let local_state = {local_state with subst; } in
        begin match T.view f with
        | TI.Bind (TI.Fun, _, _) -> assert false (* beta-reduction failed? *)
        | TI.AppBuiltin _ ->
            (* builtins are defined, but examine their args *)
            let f = mono_term ~state ~local_state f in
            let l = List.map (mono_term ~state ~local_state) l in
            T.app f l
        | TI.Const id ->
            (* find type arguments *)
            let ty = find_ty_ ~env:state.St.env id in
            let n = num_param_ty_ ty in
            (* tuple of arguments for [id] *)
            let tup = take_n_ground_atomic_types_ ~state ~local_state n l in
            (* mangle? *)
            let new_id, mangled =
              if should_be_mangled_ ~state id then mangle_ ~state id tup
              else id, None
            in
            (* specialize specialization of [id] *)
            let tup = ArgTuple.of_list ~mangled tup in
            let depth = local_state.depth + 1 in
            St.specialize ~state ~depth id tup;
            (* convert arguments.
               Drop type arguments iff they are mangled with ID *)
            let l = if mangled=None then l else CCList.drop n l in
            let l = List.map (mono_term ~state ~local_state) l in
            T.app (T.const new_id) l
        | TI.Var v ->
            (* allow variables in head (in spec/rec and in functions) *)
            begin match Subst.find ~subst:local_state.subst v with
            | None ->
                let v = mono_var ~state ~local_state v in
                let l = List.map (mono_term ~state ~local_state) l in
                T.app (T.var v) l
            | Some t ->
                mono_term ~state ~local_state (T.app t l)
            end
        | _ ->
            failf_ "cannot monomorphize application term `@[%a@]`" P.print t
        end
    | TI.Bind ((TI.Fun | TI.Forall | TI.Exists) as b, v, t) ->
        T.mk_bind b
          (mono_var ~state ~local_state v)
          (mono_term ~state ~local_state t)
    | TI.Let (v,t,u) ->
        T.let_ (mono_var ~state ~local_state v)
          (mono_term ~state ~local_state t)
          (mono_term ~state ~local_state u)
    | TI.Match (t,l) ->
        let t = mono_term ~state ~local_state t in
        let l = List.map
          (fun (c,vars,rhs) ->
            let vars = List.map (mono_var ~state ~local_state) vars in
            c, vars, mono_term ~state ~local_state rhs
          ) l
        in
        T.match_with t l
    | TI.TyMeta _ -> failwith "Mono.encode: remaining type meta-variable"
    | TI.TyBuiltin b -> T.ty_builtin b
    | TI.TyArrow (a,b) ->
        T.ty_arrow
          (mono_term ~state ~local_state a)
          (mono_term ~state ~local_state b)
    | TI.Bind (TI.TyForall,v,t) ->
        (* TODO: emit warning? *)
        assert (not (Subst.mem ~subst:local_state.subst v));
        T.ty_forall
          (mono_var ~state ~local_state v)
          (mono_term ~state ~local_state t)

  (* monomorphize a variable (rather, its type) *)
  and mono_var ~state ~local_state v =
    Var.update_ty v ~f:(mono_type ~state ~local_state)

  and mono_type ~state ~local_state t = mono_term ~state ~local_state t

  (* take [n] ground atomic type arguments in [l], or fail *)
  and take_n_ground_atomic_types_ ~state ~local_state n = function
    | _ when n=0 -> []
    | [] -> failf_ "not enough arguments (%d missing)" n
    | t :: l' ->
        let t = mono_type ~state ~local_state t in
        t :: take_n_ground_atomic_types_ ~state ~local_state (n-1) l'

  (* declare a symbol that is axiomatized *)
  and decl_sym ~state id tup =
    if not (St.is_already_declared ~state id tup) then (
      (* only declare once *)
      St.declaration_is_done ~state id tup;
      let env_info = Env.find_exn ~env:state.St.env ~id in
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

  (* specialize mutual cases *)
  let mono_cases ~state ~depth (kind, mutual_cases, case, loc) tup =
    let q = Queue.create () in (* task list, for the fixpoint *)
    let res = ref [] in (* resulting axioms *)
    (* if we required monomorphization of [id tup], and some case in [l]
       matches [id tup], then push into the queue so that it will be
       processed in the fixpoint. Otherwise, [id] must be declared/defined
       earlier and must be processed before we are done with [mutual_cases] *)
    let specialize' = St.current_specialize ~state in
    St.push_specialize ~state
      (fun ~state ~depth id tup ->
        match find_case_ ~cases:mutual_cases id tup with
        | None ->
            (* delegate to previous specialization function *)
            specialize' ~state ~depth id tup
        | Some (_cases, case, subst) ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, case, subst) q
      );
    (* push first tuple in queue *)
    begin match match_case ~case case.Stmt.case_head tup with
      | None -> ()  (* definition does not match, do nothing *)
      | Some (case, subst) ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, case, subst) q
    end;
    (* fixpoint *)
    while not (Queue.is_empty q) do
      let tup, depth, case, subst = Queue.take q in
      let id = case.Stmt.case_head in
      (* check for depth limit *)
      St.check_depth ~state depth;
      if depth > St.depth_limit ~state
      || St.is_already_specialized ~state id tup
      then ()
      else (
        NunUtils.debugf ~section 3
          "@[<2>process case `%a` for@ (%a %a)@ at depth %d@]"
          (fun k -> k P.print case.Stmt.case_defined ID.print_no_id id
            ArgTuple.print tup depth);
        St.specialization_is_done ~state id tup;
        (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
        let local_state = {subst; depth=depth+1; } in
        let axioms = List.map
          (fun ax ->
            mono_term ~state ~local_state ax
          )
          case.Stmt.case_axioms
        in
        (* new (specialized) case *)
        let case_defined = mono_term ~state ~local_state case.Stmt.case_defined in
        let case_head=TU.head_sym case_defined in (* mangled symbol now *)
        let case' = {Stmt.
          case_vars=[]; (* should be monomorphic now *)
          case_head;
          case_defined;
          case_alias=mono_var ~state ~local_state case.Stmt.case_alias;
          case_axioms=axioms;
        } in
        (* declare the symbol *)
        decl_sym ~state id tup;
        (* push new case to the list *)
        CCList.Ref.push res case';
      )
    done;
    (* remove callback *)
    St.pop_specialize ~state;
    (* push result, if any *)
    if !res <> []
    then
      let ax = match kind with
        | `Rec -> Stmt.Axiom_rec !res
        | `Spec -> Stmt.Axiom_spec !res
      in
      let stmt = Stmt.mk_axiom ~info:{Stmt.name=None; loc;} ax in
      St.push_res ~state stmt;
    ()

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
            begin match Env.find ~env:state.St.env ~id with
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
          P.print_ty tydef.Stmt.ty_type ArgTuple.print tup depth);
        St.specialization_is_done ~state tydef.Stmt.ty_id tup;
        (* mangle type name. Monomorphized type should be : Type *)
        let id, _ = mangle_ ~state tydef.Stmt.ty_id (ArgTuple.args tup) in
        let ty = T.ty_type in
        (* specialize each constructor *)
        let cstors = List.map
          (fun c ->
            (* mangle ID *)
            let id', _ = mangle_ ~state c.Stmt.cstor_name (ArgTuple.args tup) in
            (* apply, then convert type. Arity should match. *)
            let ty', subst =
              SubstUtil.ty_apply_full c.Stmt.cstor_type (ArgTuple.args tup)
            in
            let ty' = SubstUtil.eval ~subst ty' in
            let local_state = {depth=depth+1; subst} in
            let args' = List.map (mono_term ~state ~local_state) c.Stmt.cstor_args in
            {Stmt.cstor_name=id'; cstor_type=ty'; cstor_args=args'; }
          )
          tydef.Stmt.ty_cstors
        in
        (* add resulting type *)
        let tydef' = {Stmt.ty_id=id; ty_type=ty; ty_cstors=cstors; ty_vars=[]; } in
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
    let env_info = match Env.find ~env:state.St.env ~id with
      | None -> failf_ "could not find definition of %a" ID.print_name id
      | Some i -> i
    in
    let loc = Env.loc env_info in
    match Env.def env_info with
    | Env.Fun defs ->
        (* specialize each definition *)
        List.iter
          (fun def -> mono_cases ~state ~depth def tup)
          defs;
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
      (fun k-> k (NunStatement.print P.print P.print_ty) st);
    (* process statement *)
    let info = Stmt.info st in
    let loc = Stmt.loc st in
    begin match Stmt.view st with
    | Stmt.Decl (id,k,ty) ->
        (* declare the statement (in case it is needed later) *)
        Env.declare ?loc ~kind:k ~env:state.St.env id ty
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
        Env.def_funs ?loc ~kind:`Spec ~env:state.St.env l;
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        Env.def_funs ?loc ~kind:`Rec ~env:state.St.env l;
    | Stmt.TyDef (k, l) ->
        Env.def_data ?loc ~kind:k ~env:state.St.env l;
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

  let unmangle_term ~state t =
    let rec aux t = match T.view t with
      | TI.Var v -> T.var (aux_var v)
      | TI.Const id ->
          begin try
            let id', args = ID.Tbl.find state id in
            T.app (T.const id') args
          with Not_found -> t
          end
      | TI.App (f,l) -> T.app (aux f) (List.map aux l)
      | TI.AppBuiltin (b,l) -> T.app_builtin b (List.map aux l)
      | TI.Bind (b,v,t) ->
          T.mk_bind b (aux_var v) (aux t)
      | TI.Let (v,t,u) -> T.let_ (aux_var v) (aux t) (aux u)
      | TI.Match (t,l) ->
          let t = aux t in
          let l = List.map (fun (c,vars,rhs) -> c, List.map aux_var vars, aux rhs) l in
          T.match_with t l
      | TI.TyBuiltin _ -> t
      | TI.TyArrow (a,b) -> T.ty_arrow (aux a) (aux b)
      | TI.TyMeta _ -> assert false
    and aux_var = Var.update_ty ~f:aux
    in
    aux t

  (* rewrite mangled constants to their definition *)
  let unmangle_model ~state =
    NunModel.map ~f:(unmangle_term ~state)
end

(* TODO *)
module TypeMangling(T : NunTerm_ho.S) = struct
  module Trie = CCTrie.Make(struct
    type char_ = ID.t
    let compare = ID.compare
    type t = ID.t list
    let of_list l = l
    let to_seq = Sequence.of_list
  end)

  (* the state contains:

    - a prefix tree for rewriting application such as [f a b] into [f_a_b]
    - a reverse table to remember [f_a_b -> f a b] for decoding models
  *)

  type state = {
    mutable tree: ID.t Trie.t; (* [f a b --> f_a_b] *)
    rev: T.t ID.Tbl.t; (* new identifier -> monomorphized term *)
  }

  let create () = {
    tree=Trie.empty;
    rev=ID.Tbl.create 64;
  }

  let mangle_term ~state:_ _ = assert false (* TODO: traverse term, use trie *)

  let mangle_problem ~state pb =
    NunProblem.map ~term:(mangle_term ~state) ~ty:(mangle_term ~state) pb

  let unmangle_term ~state:_ _ = assert false (* TODO reverse mapping *)

  let unmangle_model ~state m =
    NunModel.map ~f:(unmangle_term ~state) m
end

let pipe_with (type a) ~decode ~print
(module T : NunTerm_ho.S with type t = a)
=
  let module Mono = Make(T) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T) in
      [Format.printf "@[<v2>after mono: %a@]@."
        (NunProblem.print ~pty_in_app:P.print_in_app P.print P.print_ty)]
    else []
  in
  NunTransform.make1
    ~on_encoded
    ~name:"monomorphization"
    ~encode:(fun p ->
      let p, state = Mono.monomorphize p in
      p, state
      (* TODO mangling of types, as an option *)
    )
    ~decode:(fun state x ->
      let decode_term = Mono.unmangle_term ~state in
      decode ~decode_term x
    )
    ()

let pipe (type a) ~print (t : (module NunTerm_ho.S with type t = a)) =
  let decode ~decode_term = NunModel.map ~f:decode_term in
  pipe_with ~print t ~decode
