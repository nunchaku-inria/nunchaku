
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
  let failf_ msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidProblem msg))

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
        fpf out "@[<h>%a -> %a@]" ID.print a ArgTupleSet.print b
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

  type unmangle_state = (ID.t * term list) ID.Tbl.t
  (* used for unmangling *)

  module St = struct
    type depth = int

    type ('inv1,'inv2) t = {
      mutable env: (term, term, ('inv1,'inv2) inv1) Env.t;
        (* access definitions/declarations by ID *)
      config: config;
        (* settings *)
      output: (term, term, ('inv1,'inv2) inv2) Stmt.t CCVector.vector;
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
      specialize: (state:('inv1,'inv2) t -> depth:depth -> ID.t -> ArgTuple.t -> unit) Stack.t;
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
        Utils.debugf ~section 1 "caution: depth limit reached" (fun k -> k);
        state.depth_reached <- true;
      )

    (* remember that (id,tup) -> mangled *)

    let save_mangled ~state id tup ~mangled =
      try Hashtbl.find state.mangle mangled
      with Not_found ->
        (* create new ID *)
        let mangled' = ID.make mangled in
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
        then Utils.debugf ~section 3 "specialize %a on %a"
          (fun k-> k ID.print id ArgTuple.print tup);
      let f = current_specialize ~state in
      f ~state ~depth id tup

    (* output statement *)
    let push_res ~state st = CCVector.push state.output st
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
  let should_be_mangled_ ~state id =
    match Env.find_exn ~env:state.St.env id with
    | {Env.def=(Env.Fun_def _ | Env.Fun_spec _ |
                Env.Cstor _ | Env.Data _ | Env.Pred _); _} ->
        true (* defined objects: mangle *)
    | {Env.def=Env.NoDef; decl_kind=(Stmt.Decl_fun | Stmt.Decl_prop); _} ->
        true (* functions and prop: mangle *)
    | {Env.def=Env.NoDef; decl_kind=Stmt.Decl_type; _} ->
        false (* uninterpreted poly types: do not mangle *)

  (* find a definition for [id] in [cases], or None *)
  let find_rec_def ~defs id =
    CCList.find_pred
      (fun def -> ID.equal (def.Stmt.rec_defined.Stmt.defined_head) id)
      defs

  (* bind the type variables of [def] to [tup]. *)
  let match_rec ?(subst=Subst.empty) ~def tup =
    assert (ArgTuple.length tup = List.length def.Stmt.rec_vars);
    Subst.add_list ~subst def.Stmt.rec_vars (ArgTuple.m_args tup)

  (* bind the type variables of [spec] to [tup]. *)
  let match_spec ?(subst=Subst.empty) ~spec tup =
    assert (ArgTuple.length tup = List.length spec.Stmt.spec_vars);
    Subst.add_list ~subst spec.Stmt.spec_vars (ArgTuple.m_args tup)

  (* find a (co)inductive type declaration for [id] *)
  let find_tydef_ ~defs id =
    CCList.find_pred
      (fun tydef -> ID.equal id tydef.Stmt.ty_id)
      defs

  (* find a definition for [id] in [cases], or None *)
  let find_pred ~defs id =
    let is_def_of (type i) id (def:(_,_,i) Stmt.pred_def) =
      ID.equal (def.Stmt.pred_defined.Stmt.defined_head) id
    in
    CCList.find_pred (is_def_of id) defs

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
        St.specialize ~state ~depth c ArgTuple.empty;
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
            let ty = find_ty_ ~env:state.St.env id in
            let n = U.ty_num_param ty in
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

  (* monomorphize a variable (rather, its type) *)
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
      let ty = U.ty_apply env_info.Env.ty (ArgTuple.args tup) in
      let new_ty = mono_type ~state ~local_state:{depth=0; subst=Subst.empty} ty in
      St.push_res ~state
        (Stmt.mk_decl ~info:{Stmt.loc; name=None}
          new_id env_info.Env.decl_kind new_ty);
    )

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
        match find_rec_def ~defs id with
        | None ->
            (* delegate to previous specialization function *)
            specialize' ~state ~depth id tup
        | Some def ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, def, match_rec ~def tup) q
      );
    (* push first tuple in queue *)
    let subst = match_rec ~def tup in
    Queue.push (tup, depth, def, subst) q;
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
        Utils.debugf ~section 3
          "@[<2>process case `%a` for@ (%a %a)@ at depth %d@]"
          (fun k -> k ID.print def.Stmt.rec_defined.Stmt.defined_head
            ID.print id ArgTuple.print tup depth);
        St.specialization_is_done ~state id tup;
        (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
        let local_state = {subst; depth=depth+1; } in
        let n = List.length def.Stmt.rec_vars in
        let eqns = mono_eqns ~state ~local_state n def.Stmt.rec_eqns
        in
        (* new (specialized) case *)
        let rec_defined = mono_defined ~state ~local_state def.Stmt.rec_defined tup in
        let def' = {Stmt.
          rec_kind=def.Stmt.rec_kind;
          rec_vars=[];
          rec_defined;
          rec_eqns=eqns;
        } in
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

  let mono_clause
  : type a b.
    state:(a, b) St.t ->
    local_state:local_state ->
    (_,_,(a,b) inv1) Stmt.pred_clause ->
    (_,_,(a,b) inv2) Stmt.pred_clause
  = fun ~state ~local_state c ->
    let open Stmt in
    let Pred_clause c = c in
    Pred_clause {
      clause_concl=mono_term ~state ~local_state c.clause_concl;
      clause_guard=CCOpt.map (mono_term ~state ~local_state) c.clause_guard;
      clause_vars=List.map (mono_var ~state ~local_state) c.clause_vars;
    }

  let mono_clauses ~state ~local_state clauses =
    List.map (mono_clause ~state ~local_state) clauses

  let mono_pred
  : type a b.
      state:(a,b) St.t -> depth:int ->
      [`Wf | `Not_wf] * [`Pred | `Copred] *
      (term, term, (a, b) inv1) Stmt.pred_def *
      (term, term, (a, b) inv1) Stmt.pred_def list * Stmt.loc option ->
      ArgTuple.t -> unit
  = fun ~state ~depth (wf, kind, def, defs, loc) tup ->
    let q = Queue.create () in (* task list, for the fixpoint *)
    let res = ref [] in (* resulting axioms *)
    (* if we required monomorphization of [id tup], and some case in [l]
       matches [id tup], then push into the queue so that it will be
       processed in the fixpoint. Otherwise, [id] must be declared/defined
       earlier and must be processed before we are done with [defs] *)
    let specialize' = St.current_specialize ~state in
    St.push_specialize ~state
      (fun ~state ~depth id tup ->
        match find_pred ~defs id with
        | None ->
            (* delegate to previous specialization function *)
            specialize' ~state ~depth id tup
        | Some def ->
            (* same mutual block, process in fixpoint. *)
            Queue.push (tup, depth, def, match_pred ~def tup) q
      );
    (* push first tuple in queue *)
    let subst = match_pred ~def tup in
    Queue.push (tup, depth, def, subst) q;
    (* fixpoint *)
    while not (Queue.is_empty q) do
      let tup, depth, def, subst = Queue.take q in
      let id = def.Stmt.pred_defined.Stmt.defined_head in
      (* check for depth limit *)
      St.check_depth ~state depth;
      if depth > St.depth_limit ~state
      || St.is_already_specialized ~state id tup
      then ()
      else (
        Utils.debugf ~section 3
          "@[<2>process pred `%a` for@ (%a %a)@ at depth %d@]"
          (fun k -> k ID.print def.Stmt.pred_defined.Stmt.defined_head
            ID.print id ArgTuple.print tup depth);
        St.specialization_is_done ~state id tup;
        (* we know [subst case.defined = (id args)], now
            specialize the axioms and other fields *)
        let local_state = {subst; depth=depth+1; } in
        let clauses = mono_clauses ~state ~local_state def.Stmt.pred_clauses in
        (* new (specialized) case *)
        let pred_defined = mono_defined ~state ~local_state def.Stmt.pred_defined tup in
        let def' = {Stmt.
          pred_tyvars=[];
          pred_defined;
          pred_clauses=clauses;
        } in
        (* push new case to the list *)
        CCList.Ref.push res def';
      )
    done;
    (* remove callback *)
    St.pop_specialize ~state;
    (* push result, if any *)
    if !res <> []
    then
      let stmt = Stmt.mk_pred ~info:{Stmt.name=None; loc;} ~wf kind !res in
      St.push_res ~state stmt;
    ()

  (* specialize specification *)
  let mono_spec ~state ~depth (spec,loc) id tup =
    assert (ArgTuple.length tup = List.length spec.Stmt.spec_vars);
    if not (St.is_already_declared ~state id tup) then (
      (* flag every symbol as specialized. We can use [tup] for every
         specified symbol, as they all share the same set of type variables. *)
      let subst = match_spec ~spec tup in
      List.iter
        (fun d ->
          let id' = d.Stmt.defined_head in
          let _, mangled = mangle_ ~state id' (ArgTuple.m_args tup) in
          let tup' = ArgTuple.make ~mangled
            ~args:(ArgTuple.args tup) ~m_args:(ArgTuple.m_args tup) in
          decl_sym ~state id' tup';
          Utils.debugf ~section 4 "@[<2>specialization of `@[<2>%a@ %a@]` is done@]"
            (fun k -> k ID.print id' ArgTuple.print tup');
          St.specialization_is_done ~state id' tup'
        )
        spec.Stmt.spec_defined;
      (* convert axioms and defined terms *)
      let defined = List.map
        (fun d -> mono_defined ~state ~local_state:{depth; subst;} d tup)
        spec.Stmt.spec_defined
      and axioms = List.map
        (fun ax -> mono_term ~state ~local_state:{depth; subst; } ax)
        spec.Stmt.spec_axioms
      in
      let st' = Stmt.axiom_spec ~info:{Stmt.loc; name=None}
        {Stmt.spec_axioms=axioms; spec_defined=defined; spec_vars=[]; }
      in
      St.push_res ~state st';
    );
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
            begin match Env.find ~env:state.St.env id with
            | Some {Env.def=Env.Data (kind', tydefs', tydef'); _} ->
                (* make id and current type mutual, even though they were not *)
                if kind <> kind'
                  then failf_
                    "@[<2>cannot handle nested {(co)data, data}:@ @[<h>{%a, %a}@]@]"
                    ID.print id ID.print tydef.Stmt.ty_id;
                tydefs := tydefs' @ !tydefs; (* bigger recursive block! *)
                Queue.push (tydef', depth, tup) q
            | _ ->
                (* not in this block, use the previous specialization fun *)
                Utils.debugf ~section 4
                  "%a not in same block, fallback to previous specialize function"
                  (fun k -> k ID.print id);
                specialize' ~state ~depth id tup
            end
        | Some tydef ->
            (* specialize in the same block of mutual types *)
            Utils.debugf ~section 4
              "%a in same block, specialize in same (co)data"
              (fun k -> k ID.print id);
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
        Utils.debugf ~section 3
          "@[<2>process type decl `%a : %a` for@ %a@ at depth %d@]"
          (fun k-> k ID.print tydef.Stmt.ty_id
          print_ty tydef.Stmt.ty_type ArgTuple.print tup depth);
        St.specialization_is_done ~state tydef.Stmt.ty_id tup;
        (* mangle type name. Monomorphized type should be : Type *)
        let id, _ =
          mangle_ ~state tydef.Stmt.ty_id (ArgTuple.m_args tup) in
        let ty = U.ty_type in
        (* specialize each constructor *)
        let cstors = ID.Map.fold
          (fun _ c acc ->
            (* mangle ID *)
            let id', _ = mangle_ ~state c.Stmt.cstor_name (ArgTuple.m_args tup) in
            (* apply, then convert type. Arity should match. *)
            let ty', subst =
              U.ty_apply_full c.Stmt.cstor_type (ArgTuple.args tup)
            in
            (* convert type and substitute in it *)
            let ty' = mono_term
              ~state ~local_state:{depth=0; subst;} ty' in
            let local_state = {depth=depth+1; subst} in
            let args' = List.map (mono_term ~state ~local_state) c.Stmt.cstor_args in
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
      | None -> failf_ "could not find definition of %a" ID.print id
      | Some i -> i
    in
    let loc = Env.loc env_info in
    match Env.def env_info with
    | Env.Fun_spec l ->
        (* specialize each definition *)
        List.iter
          (fun (spec,loc) -> mono_spec ~state ~depth (spec,loc) id tup)
          l;
        assert (St.is_already_specialized ~state id tup);
        St.specialization_is_done ~state id tup
    | Env.Fun_def (defs, def, loc) ->
        mono_rec_defs ~state ~depth (defs, def, loc) tup;
        assert (St.is_already_specialized ~state id tup);
        St.specialization_is_done ~state id tup
    | Env.Pred (wf, k, def, defs, loc) ->
        mono_pred ~state ~depth (wf, k, def, defs, loc) tup;
        assert (St.is_already_specialized ~state id tup);
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
  let mono_statement
  : type i j. state:(i,j) St.t -> (term, term, (i,j) inv1) Stmt.t -> unit
  = fun ~state st ->
    Utils.debugf ~section 2 "@[<2>enter statement@ `%a`@]"
      (fun k-> k PStmt.print st);
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
    | Stmt.Pred (wf, k, preds) ->
        state.St.env <- Env.def_preds ?loc ~env:state.St.env ~wf ~kind:k preds;
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
      (Problem.statements pb);
    (* output result. If depth limit reached we might be incomplete *)
    let meta = Problem.metadata pb in
    let meta = Problem.Metadata.add_incomplete meta state.St.depth_reached in
    let pb' = Problem.make ~meta (CCVector.freeze state.St.output) in
    (* some debug *)
    Utils.debugf ~section 3 "@[<2>instances:@ @[%a@]@]"
      (fun k-> k SetOfInstances.print state.St.already_specialized);
    pb', state.St.unmangle

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
