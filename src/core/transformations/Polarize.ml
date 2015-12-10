
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize} *)

module TI = TermInner
module Stmt = Statement
module Pol = Polarity

type ('a,'b) inv = <ty:[`Mono]; eqn:'a; ind_preds:'b>

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

  type ('a,'b) env = (term, term, ('a,'b) inv) Env.t

  type polarized_id = {
    pos: ID.t;
    neg: ID.t;
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

  let app_polarized pol p l conds =
    match pol with
    | Pol.Pos -> U.const p.pos, conds
    | Pol.Neg -> U.const p.neg, conds
    | Pol.NoPol ->
      (* choose positive, but make both equal *)
      let p1 = U.const p.pos and p2 = U.const p.neg in
      app_pol pol (U.app p1 l) (U.eq (U.app p1 l) (U.app p2 l) :: conds)

  type action =
    [ `Polarize of Pol.t
    | `Keep (* do not polarize the symbol *)
    ]

  module Trav = Traversal.Make(T)(struct
    type t = action
    let equal = (=)
    let hash _ = 0
    let print out = function
      | `Keep -> Format.fprintf out "keep"
      | `Polarize p -> Format.fprintf out "polarize(%a)" Pol.pp p
    let section = section
    let fail = errorf_
  end)

  module St = struct
    type ('a, 'b) t = {
      polarized: polarized_id option ID.Tbl.t;
        (* id -> its polarized version, if we decided to polarize it *)

      mutable call: depth:int -> ID.t -> action -> unit;
        (* callback for recursion *)

      mutable get_env: unit -> ('a, 'b) env;
    }

    let create ?(size=64) () = {
      polarized=ID.Tbl.create size;
      call=(fun ~depth:_ _ _ -> assert false);
      get_env=(fun () -> assert false);
    }

    let env ~state = state.get_env()
    let call ~state ~depth id pol = state.call ~depth id pol
  end

  let polarize_id ~state id =
    try
      match ID.Tbl.find state.St.polarized id with
      | None -> assert false
      | Some p -> p
    with Not_found ->
      let pos = ID.make_full ~needs_at:false ~pol:Pol.Pos (ID.name id) in
      let neg = ID.make_full ~needs_at:false ~pol:Pol.Neg (ID.name id) in
      let p = {pos;neg} in
      ID.Tbl.add state.St.polarized id (Some p);
      p

  let find_polarized_exn ~state id =
    match ID.Tbl.find state.St.polarized id with
    | Some p -> p
    | None -> assert false

  (* traverse [t], replacing some symbols by their polarized version,
     @return the term + a list of guards to enforce *)
  let rec polarize_rec
  : type i j. state:(i,j) St.t -> Pol.t -> T.t -> T.t * T.t list
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
                  St.call ~state ~depth:0 id (`Polarize pol);
                  let p = find_polarized_exn ~state id in
                  app_polarized pol p l conds
                ) else (
                  ID.Tbl.add state.St.polarized id None;
                  St.call ~state ~depth:0 id `Keep;
                  app_pol pol (U.app f l) conds
                )
            | Env.Pred (`Not_wf,_,_,_preds,_) ->
                (* shall polarize in all cases *)
                St.call ~state ~depth:0 id (`Polarize pol);
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
  : type a b. state:(a,b) St.t -> Pol.t -> term -> term
  = fun ~state pol t ->
    let t, conds = polarize_rec ~state pol t in
    U.and_ (t :: conds)

  (* [p] is the polarization of the function defined by [def]; *)
  let define_rec
  : type a b.
    state:(a, b) St.t -> bool ->
    (_, _, (a,b)inv) Stmt.rec_def ->
    polarized_id ->
    (_, _, (a,b)inv) Stmt.rec_def
  = fun ~state is_pos def p ->
    let open Stmt in
    let defined = def.rec_defined in
    let defined = { defined with defined_head=(if is_pos then p.pos else p.neg); } in
    let rec_eqns = map_eqns def.rec_eqns
      ~ty:CCFun.id
      ~term:(polarize_root ~state (if is_pos then Pol.Pos else Pol.Neg))
    in
    { def with
      rec_defined=defined;
      rec_eqns; }

  (* [p] is the polarization of the predicate defined by [def]; *)
  let define_pred
  : type a b.
    state:(a, b) St.t -> bool ->
    (_, _, (a,b)inv) Stmt.pred_def ->
    polarized_id ->
    (_, _, (a,b)inv) Stmt.pred_def
  = fun ~state is_pos def p ->
    let open Stmt in
    let defined = def.pred_defined in
    let defined = { defined with defined_head=(if is_pos then p.pos else p.neg); } in
    let pred_clauses =
      List.map
        (map_clause
          ~ty:CCFun.id
          ~term:(polarize_root ~state (if is_pos then Pol.Pos else Pol.Neg)))
        def.pred_clauses
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

  class ['a, 'b, 'c] traverse_pol ?(size=64) () = object(self)
    inherit [('a, 'b) inv, ('a, 'b) inv, 'c] Trav.traverse ~conf ~size ()

    val st: ('inv1, 'inv2) St.t = St.create()

    method setup() =
      st.St.call <- self#do_statements_for_id;
      st.St.get_env <- (fun () -> self#env);
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
      | `Polarize Pol.Pos ->
          let p = polarize_id ~state:st id in
          [define_rec ~state:st true def p]
      | `Polarize Pol.Neg ->
          let p = polarize_id ~state:st id in
          [define_rec ~state:st false def p]
      | `Polarize Pol.NoPol ->
          let p = polarize_id ~state:st id in
          [define_rec ~state:st true def p; define_rec ~state:st false def p]

    method do_pred ~depth:_ def act =
      let id = def.Stmt.pred_defined.Stmt.defined_head in
      if act<>`Keep
        then Utils.debugf ~section 2 "polarize (co)inductive predicate %a" (fun k->k ID.print id);
      match act with
      | `Keep ->
          let def = Stmt.map_pred def
            ~term:(polarize_root ~state:st Pol.Pos) ~ty:CCFun.id in
          [def]
      | `Polarize Pol.Pos ->
          let p = polarize_id ~state:st id in
          [define_pred ~state:st true def p]
      | `Polarize Pol.Neg ->
          let p = polarize_id ~state:st id in
          [define_pred ~state:st false def p]
      | `Polarize Pol.NoPol ->
          let p = polarize_id ~state:st id in
          [define_pred ~state:st true def p; define_pred ~state:st false def p]

    method do_term ~depth:_ t = polarize_term ~state:st t

    method do_spec ~depth:_ ~loc:_ _ _ = assert false

    method do_mutual_types ~depth:_ _ _ = assert false

    method do_ty_def ?loc:_ _ _ ~ty:_ _ = assert false
  end

  let polarize
  : (term, term, ('a,'b) inv) Problem.t ->
    (term, term, ('a,'b) inv) Problem.t * decode_state
  = fun pb ->
    let trav = new traverse_pol () in
    trav#setup();
    Problem.iter_statements pb ~f:trav#do_stmt;
    let res = trav#output in
    let pb' =
      Problem.make ~meta:(Problem.metadata pb) (CCVector.freeze res) in
    pb', ()

  (* TODO: something? do we have to merge both functions? *)
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

