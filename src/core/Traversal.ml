
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Recursive Traversal of AST} *)

module Stmt = Statement
module Loc = Location

module type ARG = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int

  val print : t CCFormat.printer
  val section : Utils.Section.t
  val fail : ('a, Format.formatter, unit, 'b) format4 -> 'a
end

module type SCC_arg = sig
  type t
  module Tbl : CCHashtbl.S with type key = t
  val deps : t -> t Sequence.t
end

(* Strongly connected components of the graph whose vertices' type is [X.t] *)
module SCC(X : SCC_arg) : sig
  val explore : X.t Sequence.t -> X.t list Sequence.t
end = struct
  module Tbl = X.Tbl

  type cell = {
    mutable min_id: int; (* min ID of the vertex' scc *)
    id: int; (* ID of the vertex *)
    mutable on_stack: bool;
    vertex: X.t;
  }

  let mk_cell v n = {
    min_id=n;
    id=n;
    on_stack=false;
    vertex=v;
  }

  (* pop elements of [stack] until we reach node with given [id] *)
  let rec pop_down_to ~id acc stack =
    assert (not (Stack.is_empty stack));
    let cell = Stack.pop stack in
    cell.on_stack <- false;
    if cell.id = id then (
      assert (cell.id = cell.min_id);
      cell.vertex :: acc (* return SCC *)
    ) else pop_down_to ~id (cell.vertex::acc) stack

  type action =
    | Enter of X.t
    | Exit_ of X.t * cell

  let explore
  : X.t Sequence.t -> X.t list Sequence.t
  = fun seq yield ->
    (* stack of nodes being explored, for the DFS *)
    let to_explore : action Stack.t = Stack.create() in
    let tbl = Tbl.create 128 in
    (* stack for Tarjan's algorithm itself *)
    let stack = Stack.create () in
    (* unique ID *)
    let count = ref 0 in
    (* exploration *)
    Sequence.iter
      (fun v ->
         Stack.push (Enter v) to_explore;
         while not (Stack.is_empty to_explore) do
           match Stack.pop to_explore with
             | Enter v ->
               if not (Tbl.mem tbl v) then (
                 (* remember unique ID for [v] *)
                 let n = !count in
                 incr count;
                 let cell = mk_cell v n in
                 cell.on_stack <- true;
                 Tbl.add tbl v cell;
                 Stack.push cell stack;
                 Stack.push (Exit_ (v, cell)) to_explore;
                 (* explore children *)
                 Sequence.iter
                   (fun e -> Stack.push (Enter e) to_explore)
                   (X.deps v)
               )
             | Exit_ (v, cell) ->
               (* update [min_id] *)
               assert cell.on_stack;
               Sequence.iter
                 (fun e ->
                    (* must not fail, [dest] already explored *)
                    let dest_cell = Tbl.find tbl e in
                    (* same SCC? yes if [dest] points to [cell.v] *)
                    if dest_cell.on_stack
                    then cell.min_id <- min cell.min_id dest_cell.min_id
                 )
                 (X.deps v);
               (* pop from stack if SCC found *)
               if cell.id = cell.min_id then (
                 let scc = pop_down_to ~id:cell.id [] stack in
                 yield scc
               )
         done
      ) seq;
    assert (Stack.is_empty stack);
    ()
end

module Make(T : TermInner.S)(Arg : ARG)(State : sig type t end) = struct
  module P = TermInner.Print(T)
  module U = TermInner.Util(T)
  module PStmt = Stmt.Print(P)(P)

  type term = T.t
  type ty = T.t

  let section = Arg.section

  module IDArgTbl = CCHashtbl.Make(struct
    type t = ID.t * Arg.t
    let equal (i1,a1)(i2,a2) = ID.equal i1 i2 && Arg.equal a1 a2
    let hash (i,a) = Hashtbl.hash (ID.hash i, Arg.hash a)
  end)

  type partial_statement_view =
    | PS_rec of (term, ty) Stmt.rec_def
    | PS_pred of [`Wf | `Not_wf] * [`Pred | `Copred] * (term, ty) Stmt.pred_def
    | PS_spec of (term, ty) Stmt.spec_defs
    | PS_decl of ty Stmt.defined
    | PS_data of [`Data | `Codata] * ty Stmt.tydef
    | PS_copy of (term, ty) Stmt.copy
    | PS_goal of term
    | PS_axiom of term list

  type partial_statement = {
    ps_view: partial_statement_view;
      (* content *)
    ps_id: int;
      (* unique identifier for this partial statement *)
    ps_info: Stmt.info;
      (* partial statements that are mutually dependent with this one,
         for dependency graph *)
  }

  let ps_equal t1 t2 = t1.ps_id = t2.ps_id
  let ps_hash t = t.ps_id land max_int

  (* fresh partial statement *)
  let mk_ps_ =
    let n = ref 0 in
    fun view ~info ->
      let ps_id = !n in
      incr n;
      { ps_view=view; ps_info=info; ps_id; }

  module PSTbl = CCHashtbl.Make(struct
      type t = partial_statement
      let equal = ps_equal
      let hash = ps_hash
    end)


  (* set of IDs defined in this (partial) statement *)
  let id_defined_by_ps ps : ID.t Sequence.t =
    let yield_defined d = Stmt.id_of_defined d |> Sequence.return in
    match ps.ps_view with
    | PS_rec d -> Stmt.defined_of_rec d |> yield_defined
    | PS_pred (_,_,d) -> Stmt.defined_of_pred d |> yield_defined
    | PS_spec l -> Stmt.defined_of_spec l |> Sequence.map Stmt.id_of_defined
    | PS_decl {Stmt.defined_head=id; _} -> Sequence.return id
    | PS_copy c -> Stmt.ids_of_copy c
    | PS_data (_,l) -> Stmt.defined_of_data l |> Sequence.map Stmt.id_of_defined
    | PS_goal _
    | PS_axiom _ -> Sequence.empty

  (* IDs used by the definition of this partial statement *)
  let deps_of_ps (ps:partial_statement) : ID.t Sequence.t =
    fun yield ->
      let yield_var v = U.to_seq_consts (Var.ty v) yield in
      let yield_vars = List.iter yield_var in
      let yield_term t = U.to_seq_consts t yield in
      let yield_defined d =
        yield (Stmt.id_of_defined d);
        yield_term (Stmt.ty_of_defined d)
      in
      begin match ps.ps_view with
        | PS_rec d ->
          begin match d.Stmt.rec_eqns with
            | Stmt.Eqn_app (ids, vars, lhs, rhs) ->
              List.iter yield ids;
              yield_vars vars;
              yield_term lhs;
              yield_term rhs
            | Stmt.Eqn_single (vars, rhs) ->
              yield_vars vars;
              yield_term rhs
            | Stmt.Eqn_nested l ->
              List.iter
                (fun (vars, args, rhs, side) ->
                   yield_vars vars;
                   List.iter yield_term args;
                   yield_term rhs;
                   List.iter yield_term side)
                l
          end
        | PS_pred (_,_,p) ->
          yield_defined p.Stmt.pred_defined;
          yield_vars p.Stmt.pred_tyvars;
          List.iter
            (fun c ->
               yield_vars c.Stmt.clause_vars;
               CCOpt.iter yield_term c.Stmt.clause_guard;
               yield_term c.Stmt.clause_concl)
            p.Stmt.pred_clauses
        | PS_spec s ->
          yield_vars s.Stmt.spec_ty_vars;
          List.iter yield_defined s.Stmt.spec_defined;
          List.iter yield_term s.Stmt.spec_axioms;
        | PS_decl {Stmt.defined_head=id; defined_ty=ty; _} ->
          yield id;
          yield_term ty
        | PS_copy c ->
          yield_vars c.Stmt.copy_vars;
          Stmt.defined_of_copy c yield_defined;
          begin match c.Stmt.copy_wrt with
            | Stmt.Wrt_nothing -> ()
            | Stmt.Wrt_subset t
            | Stmt.Wrt_quotient (_, t) -> yield_term t
          end
        | PS_goal t -> yield_term t
        | PS_axiom l -> List.iter yield_term l
        | PS_data (_,d) ->
          yield_vars d.Stmt.ty_vars;
          Stmt.defined_of_data d yield_defined
      end

  let pp_ps out ps =
    let pp_list pp = CCFormat.list ~start:"" ~stop:"" pp in
    match ps.ps_view with
      | PS_rec r ->
        Format.fprintf out "@[%a@]" PStmt.print_rec_def r
      | PS_pred (wf,k,p) ->
        Format.fprintf out "@[%s%s %a@]"
          (match k with `Pred -> "pred" | `Copred -> "copred")
          (match wf with `Wf -> "[wf]" | `Not_wf -> "")
          PStmt.print_pred_def p
      | PS_spec s ->
        Format.fprintf out "@[%a@]" PStmt.print_spec_defs s
      | PS_decl d ->
        Format.fprintf out "@[val %a@]" PStmt.pp_defined d
      | PS_data (k,d) ->
        Format.fprintf out "%s %a"
          (match k with `Data -> "data" | `Codata -> "codata")
          PStmt.print_tydef d
      | PS_copy c -> Format.fprintf out "@[copy %a@]" ID.print c.Stmt.copy_id
      | PS_axiom l ->
        Format.fprintf out "@[axiom@ %a@]" (pp_list P.print) l
      | PS_goal t -> Format.fprintf out "@[goal %a@]" P.print t

  type t = {
    max_depth: int;
      (* max recursion depth *)
    mutable env: (term, term) Env.t;
      (* input definitions *)
    state: State.t;
      (* user-defined state *)
    dispatch: dispatch;
      (* functions to process definitions and terms *)
    graph: unit IDArgTbl.t;
      (* set of (id*arg) already processed *)
    by_id: partial_statement ID.Tbl.t;
      (* new ID -> its cell in the graph *)
    new_stmts: unit PSTbl.t;
      (* set of new (partial) statements *)
    mutable depth_reached: bool;
      (* max depth reached? *)
    mutable res: (term, ty) Statement.t CCVector.vector option;
      (* result, if any *)
  }

  and dispatch = {
    do_term:
      (t -> depth:int -> term -> term);

    do_goal_or_axiom :
      (t -> depth:int -> [`Goal | `Axiom] -> term -> term) option;

    do_def:
      (t -> depth:int ->
       (term, ty) Statement.rec_def ->
       Arg.t ->
       (term, ty) Statement.rec_def);

    do_pred:
      (t -> depth:int ->
       [`Wf | `Not_wf] -> [`Pred | `Copred] ->
       (term, ty) Statement.pred_def -> Arg.t ->
       (term, ty) Statement.pred_def);

    do_copy:
      (t -> depth:int -> loc:Location.t option ->
       (term, ty) Statement.copy ->
       Arg.t ->
       (term, ty) Statement.copy)
        option;

    do_spec:
      (t -> depth:int -> loc:Location.t option ->
       ID.t ->
       (term, ty) Statement.spec_defs ->
       Arg.t ->
       (term, ty) Statement.spec_defs)
        option;

    do_data:
      (t ->
       depth:int -> [`Data | `Codata] ->
       term Statement.tydef ->
       Arg.t ->
       term Statement.tydef)
      option;

    do_ty_def:
      (t ->
       ?loc:Location.t ->
       ty Statement.defined ->
       Arg.t ->
       ty Statement.defined)
      option;
  }

  let env t = t.env
  let state t = t.state

  let processed t =
    IDArgTbl.to_seq t.graph
    |> Sequence.map fst

  let check_depth_ t d =
    if d > t.max_depth && not t.depth_reached then (
      Utils.debugf ~section 1 "caution: depth limit reached" (fun k -> k);
      t.depth_reached <- true;
    )

  (* have we processed this (id,arg) tuple? (axiom, opaque declarations…) *)
  let has_processed t (id:ID.t) (arg:Arg.t): bool =
    IDArgTbl.mem t.graph (id, arg)

  let mark_processed_ t (id:ID.t) (arg:Arg.t): unit =
    assert (not (has_processed t id arg));
    Utils.debugf ~section 4 "mark_processed `%a` (%a)"
      (fun k->k ID.print id Arg.print arg);
    IDArgTbl.add t.graph (id,arg) ()

  let mark_processed t id arg =
    if not (has_processed t id arg)
    then mark_processed_ t id arg

  (* add to the graph the vertex [as_], annotated with [ps].
     This vertex will be reachable via [id arg] *)
  let add_graph_ t (ps:partial_statement) : unit =
    PSTbl.replace t.new_stmts ps ();
    id_defined_by_ps ps
      |> Sequence.iter
        (fun id -> ID.Tbl.replace t.by_id id ps);
    ()

  let do_var_ t ~depth v : ty Var.t =
    Var.update_ty v ~f:(t.dispatch.do_term t ~depth)

  (* translate this "rec" definition *)
  let do_rec_ t ~depth ~loc (def : (_,_) Stmt.rec_def) (arg:Arg.t) : unit =
    let id = def |> Stmt.defined_of_rec |> Stmt.id_of_defined in
    Utils.debugf ~section 3
      "@[<2>@{<Cyan>process rec case@} `%a` for@ (%a)@ at depth %d@]"
      (fun k -> k ID.print id Arg.print arg depth);
    let def' = t.dispatch.do_def t ~depth def arg in
    let info = {Stmt.name=None; loc; } in
    let ps = mk_ps_ ~info (PS_rec def') in
    add_graph_ t ps;
    ()

  (* translate this "pred" definition *)
  let do_pred_ t ~depth ~loc wf k (def : (_,_) Stmt.pred_def) (arg:Arg.t) : unit =
    let id = def |> Stmt.defined_of_pred |> Stmt.id_of_defined in
    Utils.debugf ~section 3
      "@[<2>@{<Cyan>process pred case@} `%a` for@ (%a)@ at depth %d@]"
      (fun k -> k ID.print id Arg.print arg depth);
    let def' = t.dispatch.do_pred t ~depth wf k def arg in
    let info = {Stmt.name=None; loc; } in
    let ps = mk_ps_ ~info (PS_pred (wf,k,def')) in
    add_graph_ t ps;
    ()

  (* translation of toplevel goal or axiom (default is {!do_term}) *)
  let do_goal_or_axiom
    : t -> [`Goal | `Axiom] -> term -> term
    = fun t k term ->
      match t.dispatch.do_goal_or_axiom with
        | None -> t.dispatch.do_term t ~depth:0 term
        | Some f -> f t ~depth:0 k term

  exception CannotTraverse

  let traverse_stmt_ ~after_env t (st:(term,ty) Stmt.t) : unit =
    Utils.debugf ~section 2 "@[<2>enter statement@ `%a`@]"
      (fun k -> k PStmt.print st);
    (* process statement *)
    t.env <- Env.add_statement ~env:t.env st;
    after_env t.env;
    let info = Stmt.info st in
    (* most basic processing: just traverse the terms to update dependencies *)
    let tr_term () _pol term = t.dispatch.do_term t term ~depth:0 in
    let tr_type () = tr_term () Polarity.NoPol in
    let bind_var () v = (), do_var_ t ~depth:0 v in
    begin match Stmt.view st with
      | Stmt.Decl d ->
        begin match t.dispatch.do_ty_def with
          | None ->
            (* generic treatment *)
            let d = Stmt.map_defined d ~f:(tr_type ()) in
            let ps = mk_ps_ ~info (PS_decl d) in
            add_graph_ t ps
          | Some _ -> ()
        end
      | Stmt.Goal g ->
        (* convert goal *)
        let g = do_goal_or_axiom t `Goal g in
        let ps = mk_ps_ ~info (PS_goal g) in
        add_graph_ t ps
      | Stmt.Axiom (Stmt.Axiom_std l) ->
        (* keep axioms *)
        let l = List.map (do_goal_or_axiom t `Axiom) l in
        let ps = mk_ps_ ~info (PS_axiom l) in
        add_graph_ t ps
      | Stmt.Pred _
      | Stmt.Axiom (Stmt.Axiom_rec _) ->
        () (* only processed if used *)
      | Stmt.Axiom (Stmt.Axiom_spec l) ->
        begin match t.dispatch.do_spec with
          | None ->
            let s = Stmt.map_spec_defs_bind () l
                ~bind:bind_var ~term:tr_term ~ty:tr_type
            in
            let ps = mk_ps_ ~info (PS_spec s) in
            add_graph_ t ps
          | Some _ -> ()
        end
      | Stmt.Copy c ->
        begin match t.dispatch.do_copy with
          | None ->
            let c = Stmt.map_copy_bind () c ~bind:bind_var ~term:tr_term ~ty:tr_type in
            let ps = mk_ps_ ~info (PS_copy c) in
            add_graph_ t ps
          | Some _ -> ()
        end
      | Stmt.TyDef (k, l) ->
        begin match t.dispatch.do_ty_def with
          | None ->
            let l = Stmt.map_ty_defs ~ty:(tr_type ()) l in
            List.iter
              (fun d ->
                 let ps = mk_ps_ ~info (PS_data (k,d)) in
                 add_graph_ t ps)
              l
          | Some _ -> ()
        end
    end

  let traverse_stmt ?(after_env=fun _ -> ()) t st =
    if t.res <> None then raise CannotTraverse;
    traverse_stmt_ ~after_env t st

  (* [id,arg] not processed yet, traverse it depending on
     what its definition looks like *)

  let rec do_new_statement_for_id_ t ~depth id arg : unit =
    let env_info = match Env.find ~env:t.env id with
      | None -> Arg.fail "could not find definition of %a" ID.print id
      | Some i -> i
    in
    check_depth_ t depth;
    let loc = Env.loc env_info in
    match Env.def env_info with
      | Env.Fun_spec (spec,loc) ->
        begin match t.dispatch.do_spec with
          | None -> ()
          | Some f ->
            let spec' = f t ~depth ~loc id spec arg in
            let ps = mk_ps_ ~info:(Stmt.info_of_loc loc) (PS_spec spec') in
            add_graph_ t ps;
        end
      | Env.Fun_def (_defs, def, loc) ->
        do_rec_ t ~depth ~loc def arg;
      | Env.Pred (wf, k, def, _defs, loc) ->
        do_pred_ t ~depth ~loc wf k def arg;
      | Env.Cstor (_,_,tydef,_) ->
        (* instead of processing the constructor, we should always
               process the type it belongs to. *)
        call_dep t ~depth tydef.Stmt.ty_id arg
      | Env.Data (k,_tydefs,tydef) ->
        begin match t.dispatch.do_data with
          | None -> ()
          | Some f ->
            assert (ID.equal tydef.Stmt.ty_id id);
            Utils.debugf ~section 3
              "@[<2>@{<Cyan>process type decl@} `%a : %a`@ for %a@ at depth %d@]"
              (fun k-> k ID.print id P.print tydef.Stmt.ty_type Arg.print arg depth);
            let tydef' = f t ~depth k tydef arg in
            let ps = mk_ps_ ~info:(Stmt.info_of_loc loc) (PS_data (k,tydef')) in
            add_graph_ t ps;
        end
      | Env.Copy_abstract c
      | Env.Copy_concrete c
      | Env.Copy_ty c ->
        begin match t.dispatch.do_copy with
          | None -> ()
          | Some f ->
            let c' = f t ~depth ~loc c arg in
            let ps = mk_ps_ ~info:(Stmt.info_of_loc loc) (PS_copy c') in
            add_graph_ t ps;
        end
      | Env.NoDef ->
        begin match t.dispatch.do_ty_def with
          | None -> () (* already defined *)
          | Some f ->
            let ty = env_info.Env.ty in
            let attrs = env_info.Env.decl_attrs in
            let loc = env_info.Env.loc in
            let d' = f t ?loc (Stmt.mk_defined ~attrs id ty) arg in
            let ps = mk_ps_ ~info:(Stmt.info_of_loc loc) (PS_decl d') in
            add_graph_ t ps;
        end

  (* same as {!do_new_statement_for_id_}, but check if [(id,arg)] has
     been processed first *)
  and call_dep t ~depth id arg =
    if not (has_processed t id arg)
    then (
      mark_processed t id arg;
      do_new_statement_for_id_ t ~depth id arg
    )

  let create ?(size=64) ?(max_depth=256) ~env ~state ~dispatch () =
    { dispatch;
      env;
      state;
      max_depth;
      depth_reached=false;
      graph=IDArgTbl.create size;
      by_id=ID.Tbl.create size;
      new_stmts=PSTbl.create size;
      res=None;
    }

  let max_depth_reached t = t.depth_reached

  let can_merge_ ps1 ps2 =
    Utils.debugf ~section 4
      "can merge `@[%a@]`@ and `@[%a@]`" (fun k -> k pp_ps ps1 pp_ps ps2)

  let cannot_merge_ ps1 ps2 =
    Arg.fail
      "incompatible statements:@ `@[%a@]`@ and `@[%a@]`"
      pp_ps ps1 pp_ps ps2

  let merge_into_data k1 ps1 l ps = match ps.ps_view with
    | PS_data (k2,d2) ->
      if k1=k2 then (
        can_merge_ ps1 ps;
        d2 :: l
      ) else cannot_merge_ ps1 ps
    | _ -> cannot_merge_ ps1 ps

  let merge_into_pred wf1 k1 ps1 l ps = match ps.ps_view with
    | PS_pred (wf2,k2,d2) ->
      if wf1=wf2 && k1=k2 then (
        can_merge_ ps1 ps;
        d2 :: l
      ) else cannot_merge_ ps1 ps;
    | _ -> cannot_merge_ ps1 ps

  let merge_into_rec ps1 l ps = match ps.ps_view with
    | PS_rec r ->
      can_merge_ ps1 ps;
      r :: l
    | _ -> cannot_merge_ ps1 ps

  (* merge a list of [partial_statement] into one statement, or fail *)
  let stmt_of_ps_list (l : partial_statement list): (_,_) Stmt.t = match l with
    | [] -> assert false
    | {ps_view=PS_data (k1,d1); ps_info=info; _} as ps1 :: tail ->
      let l = List.fold_left (merge_into_data k1 ps1) [d1] tail in
      Stmt.mk_ty_def ~info k1 l
    | {ps_view=PS_pred (wf1,k1,p1); ps_info=info; _} as ps1 :: tail ->
      let l = List.fold_left (merge_into_pred wf1 k1 ps1) [p1] tail in
      Stmt.mk_pred ~info ~wf:wf1 k1 l
    | {ps_view=PS_rec d; ps_info=info; _} as ps1 :: tail ->
      let l = List.fold_left (merge_into_rec ps1) [d] tail in
      Stmt.axiom_rec ~info l
    | [{ps_view=PS_spec s; ps_info=info; _}] ->
      Stmt.axiom_spec ~info s
    | [{ps_view=PS_axiom l; ps_info=info; _}] ->
      Stmt.axiom ~info l
    | [{ps_view=PS_goal t; ps_info=info; _}] ->
      Stmt.goal ~info t
    | [{ps_view=PS_copy c; ps_info=info; _}] ->
      Stmt.copy ~info c
    | [{ps_view=PS_decl d; ps_info=info; _}] ->
      Stmt.decl_of_defined ~info d
    | {ps_view=(PS_decl _ | PS_axiom _ | PS_goal _ | PS_copy _ | PS_spec _); _}
      as ps1 :: ps2 :: _ ->
      Arg.fail "statement `@[%a@]`@ cannot be mutually recursive with `@[%a@]`"
        pp_ps ps1 pp_ps ps2

  (* SCC + topo sort of t.graph, output into a vector *)
  let get_statements_ t : (_,_) Stmt.t CCVector.vector =
    let find_id_ id =
      try ID.Tbl.find t.by_id id
      with Not_found ->
        Arg.fail "could not find `%a` in new graph" ID.print id
    in
    (* instantiate SCC module *)
    let module Scc = SCC(struct
        type t = partial_statement
        module Tbl = PSTbl
        let deps ps =
          deps_of_ps ps
          |> Sequence.map find_id_
      end)
    in
    (* traverse the SCC *)
    let res =
      PSTbl.to_seq t.new_stmts
      |> Sequence.map fst
      |> Scc.explore
      |> Sequence.map stmt_of_ps_list
      |> CCVector.of_seq ?init:None
    in
    (* return result *)
    res

  (* cached version of {!get_statements_} *)
  let get_statements t = match t.res with
    | Some r -> r
    | None ->
      let res = get_statements_ t in
      t.res <- Some res;
      res
end
