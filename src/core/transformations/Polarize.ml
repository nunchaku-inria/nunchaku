
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize} *)

module TI = TermInner
module Stmt = Statement
module Pol = Polarity

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

let section = Utils.Section.make "polarize"

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some (CCFormat.sprintf "@[<2>error in polarization:@ %s@]" msg)
    | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t
  type decode_state = unit

  type 'a env = (term, term, 'a inv) Env.t

  type polarized_id = {
    pos: ID.t;
    neg: ID.t;
    unroll:
      [ `Unroll_pos of ID.t
      | `Unroll_neg of ID.t
      | `Unroll_in_def of term
      (* add the given term parameter, regardless of polarity *)
      | `No_unroll];
      (* [`Unroll_pos n] means we unroll [pos] on the natural number [n]
         [`Unroll_neg n] means we unroll [neg] on [n]
         [`No_unroll] means we do not unroll either *)
  }

  let term_contains_undefined t =
    U.to_seq t
    |> Sequence.exists
      (fun t' -> match T.repr t' with
        | TI.Builtin (`Undefined _) -> true
        | _ -> false)

  (* does this set of equations contain an "undefined" sub-term? *)
  let eqns_contains_undefined
  : type i. (term, term, i) Stmt.equations -> bool
  = function
    | Stmt.Eqn_nested l ->
        List.exists
          (fun (_, args, rhs, side) ->
            List.exists term_contains_undefined args ||
            term_contains_undefined rhs ||
            List.exists term_contains_undefined side)
          l
    | Stmt.Eqn_linear l ->
        List.exists
          (fun (_, rhs, side) ->
            term_contains_undefined rhs ||
            List.exists term_contains_undefined side)
          l
    | Stmt.Eqn_single (_,rhs) ->
        term_contains_undefined rhs

  (* shall we polarize the recursive function defined as follows? *)
  let should_polarize def =
    U.ty_returns_Prop def.Stmt.rec_defined.Stmt.defined_ty
    &&
    not (eqns_contains_undefined def.Stmt.rec_eqns)

  let app_pol pol t conds = match pol with
    | Pol.Pos -> U.and_ (t :: conds), []
    | Pol.Neg -> U.imply (U.and_ conds) t, []
    | Pol.NoPol -> t, conds

  type action =
    [ `Polarize of bool
    | `Keep (* do not polarize the symbol *)
    ]

  let pp_act out = function
    | `Keep -> Format.fprintf out "keep"
    | `Polarize p -> Format.fprintf out "polarize(%B)" p

  module Trav = Traversal.Make(T)(struct
    type t = action
    let equal = (=)
    let hash _ = 0
    let print = pp_act
    let section = section
    let fail = errorf_
  end)

  module St = struct
    type 'a t = {
      polarized: polarized_id option ID.Tbl.t;
        (* id -> its polarized version, if we decided to polarize it *)

      nat: ID.t;
        (* the type of natural numbers used to make predicates well-founded *)

      succ : ID.t;

      zero: ID.t;

      mutable declared_nat : bool;
        (* have we declared nat yet? *)

      declared_decr : unit ID.Tbl.t;
        (* set of decreasing witnesses that have been declared *)

      mutable call: depth:int -> ID.t -> action -> unit;
        (* callback for recursion *)

      mutable get_env: unit -> 'a env;

      mutable add_deps : ID.t -> unit;
    }

    let create ?(size=64) () = {
      polarized=ID.Tbl.create size;
      nat=ID.make "_nat";
      succ=ID.make "_succ";
      zero=ID.make "_zero";
      declared_nat=false;
      declared_decr=ID.Tbl.create 16;
      call=(fun ~depth:_ _ _ -> assert false);
      get_env=(fun () -> assert false);
      add_deps=(fun _ -> assert false);
    }

    let nat ~state = U.const state.nat
    let succ ~state x = U.app (U.const state.succ) [x]
    let zero ~state = U.const state.zero
    let env ~state = state.get_env()
    let call ~state ~depth id pol = state.call ~depth id pol
    let add_deps ~state n = state.add_deps n
  end

  (* depending on polarity [pol], apply the proper id of [p] to
     arguments [l], along with guards [conds] *)
  let app_polarized pol p l conds =
    let l_unrolled = match pol, p.unroll with
      | _, `No_unroll -> l
      | (Pol.Pos | Pol.Neg), `Unroll_in_def t ->
          t :: l
      | Pol.NoPol, `Unroll_in_def _ ->
          assert false (* should be of uniform polarity in the definition *)
      | (Pol.Pos | Pol.NoPol), `Unroll_pos n ->
          U.const n :: l
      | (Pol.Pos | Pol.NoPol), `Unroll_neg _ -> l
      | Pol.Neg, `Unroll_neg n ->
          U.const n :: l
      | Pol.Neg, `Unroll_pos _ -> l
    in
    match pol with
    | Pol.Pos -> U.app (U.const p.pos) l_unrolled, conds
    | Pol.Neg -> U.app (U.const p.neg) l_unrolled, conds
    | Pol.NoPol ->
      (* choose positive, but make both equal *)
      let p_pos = U.const p.pos and p_neg = U.const p.neg in
      app_pol pol
        (U.app p_pos l_unrolled)
        (U.eq (U.app p_pos l_unrolled) (U.app p_neg l) :: conds)

  (* return the pair of polarized IDs for [id], with caching *)
  let polarize_id ~state ~unroll id =
    assert (not (ID.Tbl.mem state.St.polarized id));
    let pos = ID.make_full ~needs_at:false ~pol:Pol.Pos (ID.name id) in
    let neg = ID.make_full ~needs_at:false ~pol:Pol.Neg (ID.name id) in
    let p = {pos; neg; unroll} in
    ID.Tbl.add state.St.polarized id (Some p);
    p

  let find_polarized_exn ~state id =
    match ID.Tbl.find state.St.polarized id with
    | Some p -> p
    | None -> assert false

  let polarize_def_of ~state id pol = match pol with
    | Pol.Pos -> St.call ~state ~depth:0 id (`Polarize true)
    | Pol.Neg -> St.call ~state ~depth:0 id (`Polarize false)
    | Pol.NoPol ->
        (* ask for both polarities *)
        St.call ~state ~depth:0 id (`Polarize true);
        St.call ~state ~depth:0 id (`Polarize false)

  (* traverse [t], replacing some symbols by their polarized version,
     @param change if we need to add some argument
     @return the term + a list of guards to enforce *)
  let rec polarize_rec
  : type i.  state:i St.t -> Pol.t -> T.t -> T.t * T.t list
  = fun ~state pol t ->
    match T.repr t with
    | TI.Builtin (`Eq (a,b)) ->
        let a, c_a = polarize_rec ~state Pol.NoPol a in
        let b, c_b = polarize_rec ~state Pol.NoPol b in
        app_pol pol (U.eq a b) (c_a @ c_b)
    | TI.Builtin (`Equiv (a,b)) ->
        let a, c_a = polarize_rec ~state Pol.NoPol a in
        let b, c_b = polarize_rec ~state Pol.NoPol b in
        app_pol pol (U.equiv a b) (c_a @ c_b)
    | TI.Builtin (`Ite (a,b,c)) ->
        let a, c_a = polarize_rec ~state pol a in
        let b, c_b = polarize_rec ~state pol b in
        let c, c_c = polarize_rec ~state pol c in
        app_pol pol (U.ite a b c) (U.ite a (U.and_ c_b) (U.and_ c_c) :: c_a)
    | TI.Builtin _
    | TI.Var _
    | TI.Const _ -> t, []
    | TI.App (f,l) ->
        (* convert arguments *)
        let conds, l = CCList.fold_map
          (fun conds t ->
            let t, c_t = polarize_rec ~state Pol.NoPol t in
            c_t @ conds, t)
          [] l
        in
        begin match T.repr f, l with
        | TI.Const id, _ when ID.Tbl.mem state.St.polarized id ->
            (* we already chose whether [id] was polarized or not *)
            begin match ID.Tbl.find state.St.polarized id with
            | None ->
                St.call ~state ~depth:0 id `Keep;
                app_pol pol (U.app f l) conds
            | Some p ->
                polarize_def_of ~state id pol;
                app_polarized pol p l conds
            end
        | TI.Const id, _ ->
            (* shall we polarize this constant? *)
            let info = Env.find_exn ~env:(St.env ~state) id in
            begin match Env.def info with
            | Env.NoDef
            | Env.Data (_,_,_)
            | Env.Cstor (_,_,_,_)
            | Env.Pred (`Wf,_,_,_,_)
            | Env.Fun_spec _ ->
                (* do not polarize *)
                ID.Tbl.add state.St.polarized id None;
                St.call ~state ~depth:0 id `Keep;
                app_pol pol (U.app f l) conds
            | Env.Fun_def (_defs,def,_) ->
                (* we can polarize, or not: delegate to heuristic *)
                if should_polarize def
                then (
                  polarize_def_of ~state id pol;
                  let p = find_polarized_exn ~state id in
                  app_polarized pol p l conds
                ) else (
                  ID.Tbl.add state.St.polarized id None;
                  St.call ~state ~depth:0 id `Keep;
                  app_pol pol (U.app f l) conds
                )
            | Env.Pred (`Not_wf,_,_,_preds,_) ->
                (* shall polarize in all cases *)
                polarize_def_of ~state id pol;
                let p = find_polarized_exn ~state id in
                app_polarized pol p l conds
            end
        | TI.Builtin `Imply, [a;b] ->
            let a, c_a = polarize_rec ~state (Pol.inv pol) a in
            let b, c_b = polarize_rec ~state pol b in
            app_pol pol (U.imply a b) (c_a @ c_b)
        | _ ->
            app_pol pol (U.app f l) conds
        end
    | TI.Bind ((`Forall | `Exists) as b,v,t) ->
        let t, conds = polarize_rec ~state pol t in
        app_pol pol (U.mk_bind b v t) conds
    | TI.Bind (`Fun,v,t) ->
        (* no polarity *)
        let t, conds = polarize_rec ~state Pol.NoPol t in
        app_pol pol (U.fun_ v t) conds
    | TI.Bind (`TyForall, _, _) ->
        assert false  (* we do not polarize in types *)
    | TI.Let (v,t,u) ->
        (* we don't know the polarity of [t] in [u], so we prepare for
           the worst case *)
        let t, c_t = polarize_rec ~state Pol.NoPol t in
        let u, c_u = polarize_rec ~state pol u in
        app_pol pol (U.let_ v t u) (U.let_ v t (U.and_ c_u) :: c_t @ c_u)
    | TI.Match (t,l) ->
        let t, c_t = polarize_rec ~state Pol.NoPol t in
        let conds = ref [] in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let rhs, c_rhs = polarize_rec ~state pol rhs in
            conds := c_rhs @ !conds;
            vars, rhs)
          l
        in
        app_pol pol (U.match_with t l) (c_t @ !conds)
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, []
    | TI.TyMeta _ -> assert false

  and polarize_root
  : type a. state:a St.t -> Pol.t -> term -> term
  = fun ~state pol t ->
    let t, conds = polarize_rec ~state pol t in
    U.and_ (t :: conds)

  (* [p] is the polarization of the function defined by [def]; *)
  let define_rec
  : type a.
    state:a St.t -> bool ->
    (_, _, a inv) Stmt.rec_def ->
    polarized_id ->
    (_, _, a inv) Stmt.rec_def
  = fun ~state is_pos def p ->
    let open Stmt in
    assert (p.unroll = `No_unroll);
    let defined = def.rec_defined in
    let defined = { defined with defined_head=(if is_pos then p.pos else p.neg); } in
    let rec_eqns = map_eqns def.rec_eqns
      ~ty:CCFun.id
      ~term:(polarize_root ~state (if is_pos then Pol.Pos else Pol.Neg))
    in
    { def with
      rec_defined=defined;
      rec_eqns; }

  (* make a variable for each type *)
  let make_vars tys =
    List.mapi (fun i ty -> Var.make ~name:(CCFormat.sprintf "v_%d" i) ~ty) tys

  (* replace [id]' polarized with [p] locally *)
  let with_local_polarized ~state id p ~f =
    ID.Tbl.add state.St.polarized id (Some p);
    CCFun.finally
      ~h:(fun () -> ID.Tbl.remove state.St.polarized id)
      ~f

  (* [p] is the polarization of the predicate defined by [def]; *)
  let define_pred
  : type a.
    state:a St.t ->
    is_pos:bool ->
    (_, _, a inv) Stmt.pred_def ->
    polarized_id ->
    (_, _, a inv) Stmt.pred_def
  = fun ~state ~is_pos def p ->
    let open Stmt in
    let defined = def.pred_defined in
    let id = defined.defined_head in
    let defined =
      { Stmt.
        defined_head=(if is_pos then p.pos else p.neg);
        defined_ty=(match p.unroll, is_pos with
          | `Unroll_pos _, true
          | `Unroll_neg _, false ->
              (* add a parameter of type [nat] that will decrease at every call *)
              U.ty_arrow (St.nat ~state) defined.Stmt.defined_ty
          | _ -> defined.Stmt.defined_ty
        );
      } in
    (* TODO: if `Unroll, define the clauses slightly differently, by
       adding a 0 case (true or false dep. on polarity)
       and adding n ==> (s n) in every guarded clause *)
    let unroll_clause
      : type a.
          (term, term, a inv) pred_clause ->
          (term, term, a inv) pred_clause
      = fun ((Pred_clause c) as clause) ->
        let pol = if is_pos then Pol.Pos else Pol.Neg in
        match p.unroll, is_pos with
        | `Unroll_pos _, true
        | `Unroll_neg _, false ->
            (* add a new variable of type nat, that will decrease from
               conclusion to guard *)
            let v = Var.make ~name:"_decr" ~ty:(St.nat ~state) in
            Pred_clause {
              clause_vars = v :: c.clause_vars;
              clause_guard =
                (* in guard, replace [pred] by [pred (S v)] *)
                CCOpt.map
                  (fun g ->
                    let additional_param = U.var v in
                    let p' = { p with unroll=`Unroll_in_def additional_param; } in
                    with_local_polarized ~state id p'
                      ~f:(fun () -> polarize_root ~state pol g))
                  c.clause_guard;
              clause_concl =
                (* in concl, replace [pred] by [pred v] *)
                let additional_param = St.succ ~state (U.var v) in
                let p' = { p with unroll=`Unroll_in_def additional_param; } in
                with_local_polarized ~state id p'
                  ~f:(fun () -> polarize_root ~state pol c.clause_concl);
            }
        | _ ->
            map_clause clause ~ty:CCFun.id ~term:(polarize_root ~state pol)
    in
    let pred_clauses = List.map unroll_clause def.pred_clauses in
    (* if we unroll a coinductive predicate in negative polarity,
       we must add a base case [pred 0 _...._ = true].
       We don't need anything for the inductive predicate
       because [pred 0 _ = false] is the default semantic *)
    let pred_clauses = match p.unroll, is_pos with
      | `Unroll_neg _, false ->
          let _, ty_args, _ = U.ty_unfold def.pred_defined.defined_ty in
          let vars = make_vars ty_args in
          let vars_t = List.map U.var vars in
          let c = Pred_clause {
            clause_vars = vars;
            clause_guard = None;
            clause_concl = U.app (U.const p.neg) (St.zero ~state :: vars_t);
          } in
          c :: pred_clauses
      | _ -> pred_clauses
    in
    { def with
      pred_defined=defined;
      pred_clauses; }

  let polarize_term ~state t = polarize_root ~state Pol.NoPol t

  let conf = {Traversal.
    direct_tydef=true;
    direct_spec=true;
    direct_mutual_types=true;
  }

  class ['a, 'c] traverse_pol ?(size=64) () = object(self)
    inherit ['a inv, 'a inv, 'c] Trav.traverse ~conf ~size ()

    val st: 'inv1 St.t = St.create ()

    method setup() =
      st.St.call <- self#do_statements_for_id;
      st.St.get_env <- (fun () -> self#env);
      st.St.add_deps <- (fun n-> self#add_deps n);
      ()

    method do_def ~depth:_ def act =
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      if act<>`Keep
        then Utils.debugf ~section 5 "polarize def %a" (fun k->k ID.print id);
      match act with
      | `Keep ->
          let def = Stmt.map_rec_def def
            ~term:(polarize_root ~state:st Pol.Pos) ~ty:CCFun.id in
          [def]
      | `Polarize true ->
          let p = polarize_id ~state:st ~unroll:`No_unroll id in
          [define_rec ~state:st true def p]
      | `Polarize false ->
          let p = polarize_id ~state:st ~unroll:`No_unroll id in
          [define_rec ~state:st false def p]

    (* declare the type [nat] *)
    method private declare_nat =
      let ty_nat = U.const st.St.nat in
      let def = Stmt.mk_mutual_ty st.St.nat
          ~ty_vars:[]
          ~ty:U.ty_type
          ~cstors:
            [ st.St.zero, [], ty_nat
            ; st.St.succ, [ty_nat], U.ty_arrow ty_nat ty_nat]
      in
      self#push_res
        (Stmt.data ~info:Stmt.info_default [def]);
      ()

    (* declare the constant [n] of type [nat], to be used for unrolling *)
    method private add_deps n =
      if not st.St.declared_nat then (
        st.St.declared_nat <- true;
        self#declare_nat
      );
      if not (ID.Tbl.mem st.St.declared_decr n) then (
        ID.Tbl.add st.St.declared_decr n ();
        let ty = St.nat ~state:st in
        (* declare n:nat *)
        self#push_res (Stmt.decl ~info:Stmt.info_default n ty);
      )

    (* by unrolling, we make every (co)inductive predicate well-founded *)
    method! pred_translate_wf _ = `Wf

    method do_pred ~depth:_ wf kind def act =
      let id = def.Stmt.pred_defined.Stmt.defined_head in
      if act<>`Keep
      then
        Utils.debugf ~section 2 "polarize (co)inductive predicate %a on (%a)"
         (fun k->k ID.print id pp_act act);
      match act with
      | `Keep ->
          let def = Stmt.map_pred def
            ~term:(polarize_root ~state:st Pol.Pos) ~ty:CCFun.id in
          [def]
      | `Polarize is_pos ->
          let p =
            try
              match ID.Tbl.find st.St.polarized id with
              | None -> assert false (* incompatible *)
              | Some p -> p
            with Not_found ->
              (* shall we unroll one of the polarized predicates? *)
              let unroll = match wf, kind with
                | `Wf, _
                | `Not_wf, `Pred ->
                    let n = ID.make (CCFormat.sprintf "decr_%a" ID.print_name id) in
                    St.add_deps ~state:st n;
                    `Unroll_pos n
                | `Not_wf, `Copred ->
                    let n = ID.make (CCFormat.sprintf "decr_%a" ID.print_name id) in
                    St.add_deps ~state:st n;
                    `Unroll_neg n
              in
              let p = polarize_id ~state:st ~unroll id in
              p
          in
          if is_pos
          then [define_pred ~state:st ~is_pos:true def p]
          else [define_pred ~state:st ~is_pos:false def p]

    method do_term ~depth:_ t = polarize_term ~state:st t

    method do_spec ~depth:_ ~loc:_ _ _ = assert false

    method do_mutual_types ~depth:_ _ _ = assert false

    method do_ty_def ?loc:_ _ _ ~ty:_ _ = assert false
  end

  let polarize
  : (term, term, 'a inv) Problem.t ->
    (term, term, 'a inv) Problem.t * decode_state
  = fun pb ->
    let trav = new traverse_pol () in
    trav#setup();
    Problem.iter_statements pb ~f:trav#do_stmt;
    let res = trav#output in
    let pb' =
      Problem.make ~meta:(Problem.metadata pb) (CCVector.freeze res) in
    pb', ()

  (* TODO: something? do we have to merge both functions?

   - also, remember unrolling, so that the additional decreasing parameter
    is erased from all subterms in the model
    (might be done via rewriting, say, [pred+ _ → pred])

  *)
  let decode_model ~state:_ m = m

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after polarization:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"polarize"
      ~on_encoded
      ~encode:(fun pb -> polarize pb)
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end

