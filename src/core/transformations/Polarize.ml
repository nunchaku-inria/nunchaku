
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

  type 'a env = (term, term, 'a inv) Env.t

  type polarized_id = {
    pos: ID.t;
    neg: ID.t;
    unroll:
      [ `No_unroll
      | `Unroll_pos of ID.t
      | `Unroll_neg of ID.t
      | `Unroll_in_def of term
          (* add the given term parameter, regardless of polarity *)
      ];
    (* [`Unroll_pos n] means we unroll [pos] on the natural number [n]
       [`Unroll_neg n] means we unroll [neg] on [n]
       [`No_unroll] means we do not unroll either *)
  }

  (* the type of natural numbers used to make predicates well-founded, and its
     constructors *)
  type nat_ty = {
    nat: ID.t;
    succ : ID.t;
    zero: ID.t;
  }

  type decode_state = {
    rev_map: (ID.t * bool * polarized_id) ID.Tbl.t;
      (* polarized_id -> (original_id, polarity, unroll) *)

    rev_nat: nat_ty;
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

      polarize_rec: bool;
        (* enable/disable polarization of predicates defined with `rec` *)

      nat_ty : nat_ty;

      mutable declared_nat : bool;
        (* have we declared nat yet? *)

      declared_decr : unit ID.Tbl.t;
        (* set of decreasing witnesses that have been declared *)

      decode_state : decode_state;
        (* for decoding *)

      mutable call: depth:int -> ID.t -> action -> unit;
        (* callback for recursion *)

      mutable get_env: unit -> 'a env;

      mutable add_deps : ID.t -> unit;
    }

    let create ?(size=64) ~polarize_rec () =
      let nat_ty = {
        nat=ID.make "_nat";
        succ=ID.make "_succ";
        zero=ID.make "_zero";
      } in
      { polarized=ID.Tbl.create size;
        polarize_rec;
        declared_nat=false;
        declared_decr=ID.Tbl.create 16;
        nat_ty;
        decode_state = {
          rev_map=ID.Tbl.create 32;
          rev_nat=nat_ty;
        };
        call=(fun ~depth:_ _ _ -> assert false);
        get_env=(fun () -> assert false);
        add_deps=(fun _ -> assert false);
    }

    let nat ~state = U.const state.nat_ty.nat
    let succ ~state x = U.app (U.const state.nat_ty.succ) [x]
    let zero ~state = U.const state.nat_ty.zero
    let env ~state = state.get_env()
    let call ~state ~depth id pol = state.call ~depth id pol
    let add_deps ~state n = state.add_deps n
  end

  (* shall we polarize the recursive function defined as follows? *)
  let should_polarize ~state def =
    state.St.polarize_rec (* option enabled? *)
    &&
    let _, ty_args, ty_ret = U.ty_unfold def.Stmt.rec_defined.Stmt.defined_ty in
    U.ty_is_Prop ty_ret
    &&
    List.length ty_args > 0 (* function, not constant *)
    &&
    not (eqns_contains_undefined def.Stmt.rec_eqns)

  (* depending on polarity [pol], apply the proper id of [p] to
     arguments [l], along with guards [conds] *)
  let app_polarized pol p l =
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
    | Pol.Pos -> U.app (U.const p.pos) l_unrolled
    | Pol.Neg -> U.app (U.const p.neg) l_unrolled
    | Pol.NoPol ->
      (* choose positive, but make both equal *)
      let p_pos = U.const p.pos and p_neg = U.const p.neg in
      let t = U.app p_pos l_unrolled in
      (* force p_pos = p_neg here *)
      U.asserting t [ U.eq (U.app p_pos l_unrolled) (U.app p_neg l) ]

  (* return the pair of polarized IDs for [id], with caching *)
  let polarize_id ~state ~unroll id =
    assert (not (ID.Tbl.mem state.St.polarized id));
    let pos = ID.make_full ~needs_at:false ~pol:Pol.Pos (ID.name id) in
    let neg = ID.make_full ~needs_at:false ~pol:Pol.Neg (ID.name id) in
    let p = {pos; neg; unroll} in
    ID.Tbl.add state.St.polarized id (Some p);
    (* reverse mapping, for decoding *)
    ID.Tbl.add state.St.decode_state.rev_map pos (id, true, p);
    ID.Tbl.add state.St.decode_state.rev_map neg (id, false, p);
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
     @return the term with more internal guards and polarized symbols *)
  let rec polarize_term_rec
  : type i.  state:i St.t -> Pol.t -> T.t -> T.t
  = fun ~state pol t ->
    match T.repr t with
    | TI.Builtin (`Eq (a,b)) ->
        let a = polarize_term_rec ~state Pol.NoPol a in
        let b = polarize_term_rec ~state Pol.NoPol b in
        U.eq a b
    | TI.Builtin (`Equiv (a,b)) ->
        let a = polarize_term_rec ~state Pol.NoPol a in
        let b = polarize_term_rec ~state Pol.NoPol b in
        U.equiv a b
    | TI.Builtin (`Ite (a,b,c)) ->
        let a = polarize_term_rec ~state pol a in
        let b = polarize_term_rec ~state pol b in
        let c = polarize_term_rec ~state pol c in
        U.ite a b c
    | TI.Builtin (`Guard (t, g)) ->
        let g = TI.Builtin.map_guard (polarize_term_rec ~state pol) g in
        let t = polarize_term_rec ~state pol t in
        U.guard t g
    | TI.Builtin _
    | TI.Var _
    | TI.Const _ -> t
    | TI.App (f,l) ->
        (* convert arguments *)
        let l = List.map (polarize_term_rec ~state Pol.NoPol) l in
        begin match T.repr f, l with
        | TI.Const id, _ when ID.Tbl.mem state.St.polarized id ->
            (* we already chose whether [id] was polarized or not *)
            begin match ID.Tbl.find state.St.polarized id with
            | None ->
                St.call ~state ~depth:0 id `Keep;
                U.app f l
            | Some p ->
                polarize_def_of ~state id pol;
                app_polarized pol p l
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
                U.app f l
            | Env.Fun_def (_defs,def,_) ->
                (* we can polarize, or not: delegate to heuristic *)
                if should_polarize ~state def
                then (
                  polarize_def_of ~state id pol;
                  let p = find_polarized_exn ~state id in
                  app_polarized pol p l
                ) else (
                  ID.Tbl.add state.St.polarized id None;
                  St.call ~state ~depth:0 id `Keep;
                  U.app f l
                )
            | Env.Pred (`Not_wf,_,pred,_preds,_) ->
                let ty = pred.Stmt.pred_defined.Stmt.defined_ty in
                if U.ty_is_Prop ty then (
                  (* constant: degenerate case of (co)inductive pred, no need
                     for polarization, and necessarily WF. *)
                  ID.Tbl.add state.St.polarized id None;
                  St.call ~state ~depth:0 id `Keep;
                  assert (l = []);
                  f
                ) else (
                  (* polarize *)
                  polarize_def_of ~state id pol;
                  let p = find_polarized_exn ~state id in
                  app_polarized pol p l
                )
            end
        | TI.Builtin `Imply, [a;b] ->
            let a = polarize_term_rec ~state (Pol.inv pol) a in
            let b = polarize_term_rec ~state pol b in
            U.imply a b
        | _ -> U.app f l
        end
    | TI.Bind ((`Forall | `Exists) as b,v,t) ->
        let t = polarize_term_rec ~state pol t in
        U.mk_bind b v t
    | TI.Bind (`Fun,v,t) ->
        (* no polarity *)
        let t = polarize_term_rec ~state Pol.NoPol t in
        U.fun_ v t
    | TI.Bind (`TyForall, _, _) ->
        assert false  (* we do not polarize in types *)
    | TI.Let (v,t,u) ->
        (* we don't know the polarity of [t] in [u], so we prepare for
           the worst case *)
        let t = polarize_term_rec ~state Pol.NoPol t in
        let u = polarize_term_rec ~state pol u in
        U.let_ v t u
    | TI.Match (lhs,l) ->
        let lhs = polarize_term_rec ~state Pol.NoPol lhs in
        let l = ID.Map.map
          (fun (vars,rhs) -> vars, polarize_term_rec ~state pol rhs)
          l
        in
        U.match_with lhs l
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t
    | TI.TyMeta _ -> assert false

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
      ~term:(polarize_term_rec ~state (if is_pos then Pol.Pos else Pol.Neg))
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
    (* if `Unroll, define the clauses slightly differently, by
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
                      ~f:(fun () -> polarize_term_rec ~state pol g))
                  c.clause_guard;
              clause_concl =
                (* in concl, replace [pred] by [pred v] *)
                let additional_param = St.succ ~state (U.var v) in
                let p' = { p with unroll=`Unroll_in_def additional_param; } in
                with_local_polarized ~state id p'
                  ~f:(fun () -> polarize_term_rec ~state pol c.clause_concl);
            }
        | _ ->
            map_clause clause ~ty:CCFun.id ~term:(polarize_term_rec ~state pol)
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

  let polarize_term ~state t = polarize_term_rec ~state Pol.NoPol t

  let conf = {Traversal.
    direct_tydef=true;
    direct_spec=true;
    direct_mutual_types=true;
  }

  class ['a, 'c] traverse_pol ?(size=64) ~polarize_rec () = object(self)
    inherit ['a inv, 'a inv, 'c] Trav.traverse ~conf ~size ()

    val st: 'inv1 St.t = St.create ~polarize_rec ()

    method setup() =
      st.St.call <- self#do_statements_for_id;
      st.St.get_env <- (fun () -> self#env);
      st.St.add_deps <- (fun n-> self#add_deps n);
      ()

    method decode_state = st.St.decode_state

    method do_def ~depth:_ def act =
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      if act<>`Keep
        then Utils.debugf ~section 5 "polarize def %a on %a"
          (fun k->k ID.print id pp_act act);
      match act with
      | `Keep ->
          let def = Stmt.map_rec_def def
            ~term:(polarize_term_rec ~state:st Pol.Pos) ~ty:CCFun.id in
          [def]
      | `Polarize is_pos ->
          let p =
            try match ID.Tbl.find st.St.polarized id with
              | None -> assert false
              | Some p -> p
            with Not_found ->
              polarize_id ~state:st ~unroll:`No_unroll id
          in
          [define_rec ~state:st is_pos def p]

    (* declare the type [nat] *)
    method private declare_nat =
      let ty_nat = St.nat ~state:st in
      let def = Stmt.mk_mutual_ty st.St.nat_ty.nat
          ~ty_vars:[]
          ~ty:U.ty_type
          ~cstors:
            [ st.St.nat_ty.zero, [], ty_nat
            ; st.St.nat_ty.succ, [ty_nat], U.ty_arrow ty_nat ty_nat]
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
            ~term:(polarize_term_rec ~state:st Pol.Pos) ~ty:CCFun.id in
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
          [define_pred ~state:st ~is_pos def p]

    method do_term ~depth:_ t = polarize_term ~state:st t

    method do_spec ~depth:_ ~loc:_ _ _ = assert false

    method do_mutual_types ~depth:_ _ _ = assert false

    method do_ty_def ?loc:_ _ _ ~ty:_ _ = assert false
  end

  let polarize
  : polarize_rec:bool ->
    (term, term, 'a inv) Problem.t ->
    (term, term, 'a inv) Problem.t * decode_state
  = fun ~polarize_rec pb ->
    let trav = new traverse_pol ~polarize_rec () in
    trav#setup();
    Problem.iter_statements pb ~f:trav#do_stmt;
    let res = trav#output in
    let pb' =
      Problem.make ~meta:(Problem.metadata pb) (CCVector.freeze res) in
    pb', trav#decode_state

  (** {6 Decoding} *)

  module U_dt = Model.DT_util(T)

  (* rewrite the term recursively.
     Rules are of the form:
    - [id -> id', `Rm_0] means [id] should be rewritten into [id']
    - [id -> id', `Rm_1] means [id _] should be rewritten into [id']
    *)
  let rec rewrite sys t =
    (* rewrite subterms first *)
    let t = U.map () t
      ~f:(fun () t -> rewrite sys t)
      ~bind:(fun () v -> (), v)
    in
    match T.repr t with
    | TI.Const id ->
        begin try
          let id', act = ID.Map.find id sys in
          if act=`Rm_0 then U.const id' else assert false
        with Not_found -> t
        end
    | TI.App (f, l) ->
        begin match T.repr f, l with
        | _, [] -> assert false
        | TI.Const id, _ :: l' ->
            begin try
              let id', act = ID.Map.find id sys in
              match act with
              | `Rm_0 -> U.app (U.const id') l
              | `Rm_1 -> U.app (U.const id') l'  (* remove first arg *)
            with Not_found -> t
            end
        | _ -> t
        end
    | _ -> t

  (* filter [dt], the decision tree for [polarized], returning
     only the cases that return [true] (if [is_pos]) or [false] (if [not is_pos]) *)
  let filter_dt_ ~is_pos ~polarized ~sys ~removed_var dt =
    Utils.debugf ~section 5
      "@[<v>filter occurrences of polarity %B for `%a`@ removing var (@[%a@])@ from `@[%a@]`@]"
      (fun k->k
        is_pos ID.print polarized (CCFormat.opt Var.print_full) removed_var
        (Model.DT.print P.print) dt);
    CCList.filter_map
      (fun (eqns, then_) ->
        match T.repr then_, is_pos with
        | TI.Builtin `True, true
        | TI.Builtin `False, false ->
            let eqns' =
              CCList.filter_map
                (fun (v, t) ->
                  match removed_var with
                  | Some v' when Var.equal v v' -> None (* remove test *)
                  | _ ->
                      (* otherwise just rewrite the term *)
                      Some (v, rewrite sys t))
                eqns
            in
            let then' = rewrite sys then_ in
            Some (eqns', then')
        | TI.Builtin `False, true
        | TI.Builtin `True, false -> None
        | _ ->
            errorf_
              "@[<2>expected decision tree for %a@ to yield only true/false@ \
               but branch `@[%a@]`@ yields `@[%a@]`@]"
               ID.print polarized
               (Model.DT.print_tests P.print) eqns
               P.print then_)
      dt.Model.DT.tests

  (* build a rewrite system from the given model. The rewrite system erases
     polarities and unrolling parameters. *)
  let make_rw_sys_ ~state m =
    Model.fold ID.Map.empty m
      ~constants:(fun sys _ -> sys)
      ~finite_types:(fun sys _ -> sys)
      ~funs:(fun sys (t,_,_) ->
        match T.repr t with
        | TI.Const id when ID.is_polarized id ->
            (* rewrite into the unpolarized version *)
            let id', is_pos, p = ID.Tbl.find state.rev_map id in
            let act = match is_pos, p.unroll with
              | true, `Unroll_pos _
              | false, `Unroll_neg _ ->
                  `Rm_1 (* [id _ --> id'], to remove the unroll invariant *)
              | _ -> `Rm_0 (* just [id --> id'] *)
            in
            Utils.debugf ~section 4 "@[<2>decoding:@ rewrite %a into %a, %s@]"
              (fun k->k ID.print id ID.print id'
                (match act with `Rm_0 -> "rm0" | `Rm_1 -> "rm1"));
            ID.Map.add id (id', act) sys
        | _ -> sys)

  (* decoding:
    - keep positive cases for p+, negative cases for p-, and undefined otherwise
    - remove the additional parameter introduced by unrolling, if any
  *)
  let decode_model ~state m =
    (* compute a rewrite system for eliminating polarized IDs *)
    let sys = make_rw_sys_ ~state m in
    (* this tables stores the half-decision tree for polarized IDs
       (when we have met one polarity but not the other *)
    let partial_map = ID.Tbl.create 32 in
    Model.filter_map m
      ~constants:(fun (t,u) ->
        match T.repr t with
        | TI.Const id when ID.equal id state.rev_nat.zero ->
            None (* remove "zero" *)
        | _ ->
            let u = rewrite sys u in
            Some (t,u))
      ~finite_types:(fun (t,dom) ->
        match T.repr t with
        | TI.Const id when ID.equal id state.rev_nat.nat ->
            None (* remove "nat" *)
        | _ -> Some (t,dom))
      ~funs:(fun (t,vars,dt) ->
        match T.repr t with
        | TI.Const id when ID.equal id state.rev_nat.succ ->
            None (* remove "succ" *)
        | TI.Const id when ID.is_polarized id ->
            (* unpolarize. id' is the unpolarized ID. *)
            let id', is_pos, p = ID.Tbl.find state.rev_map id in
            (* do we need to remove a variable? *)
            let removed_var, vars = match is_pos, p.unroll, vars with
              | true, `Unroll_pos _, v :: vars'
              | false, `Unroll_neg _, v :: vars' -> Some v, vars'
              | _, (`Unroll_pos _ | `Unroll_neg _), [] -> assert false
              | _ -> None, vars
            in
            let cases = filter_dt_ ~polarized:id ~is_pos ~sys ~removed_var dt in
            begin try
              (* if [id' in partial_map], we already met its other polarized
                 version, so we can merge the decision trees and push [id']
                 in the model. *)
              let cases' = ID.Tbl.find partial_map id' in
              (* merge the two partial decision trees — they should not overlap *)
              let else_ = U.undefined_ (U.app (U.const id') (List.map U.var vars)) in
              let new_dt =
                Model.DT.test
                  (List.rev_append cases cases')
                  ~else_
              in
              (* emit model for [id'] *)
              Some (U.const id', vars, new_dt)
            with Not_found ->
              (* store the decision tree in [partial_map]; [id'] will
                 be added to the model when its second polarized version
                 is met *)
              ID.Tbl.add partial_map id' cases;
              None
            end
        | _ ->
            (* remove polarized IDs *)
            let dt = Model.DT.map dt ~term:(rewrite sys) ~ty:CCFun.id in
            Some (t,vars,dt))

  (** {6 Pipes} *)

  let pipe_with ~decode ~polarize_rec ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after polarization:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"polarize"
      ~on_encoded
      ~encode:(fun pb -> polarize ~polarize_rec pb)
      ~decode
      ()

  let pipe ~polarize_rec ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~polarize_rec ~print
end

