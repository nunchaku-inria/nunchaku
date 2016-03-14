
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unrolling of (co)inductive Predicates} *)

module TI = TermInner
module Stmt = Statement
module Pol = Polarity

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

let name = "unroll"
let section = Utils.Section.make name

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)

  type term = T.t

  type unroll =
      [ `Unroll of ID.t
      | `Unroll_in_def of term
      ]
    (* [`Unroll n] means we unroll the ID on the natural number [n]
       [`Unroll_in_def t] means we are in the definition of the ID, and
        use [t] as the unrolling parameter *)

  (* the type of natural numbers used to make predicates well-founded, and its
     constructors *)
  type nat_ty = {
    nat: ID.t;
    succ : ID.t;
    zero: ID.t;
  }

  type state = {
    map: unroll ID.Tbl.t;
      (* polarized ID -> unrolling for this ID *)

    nat_ty: nat_ty;
      (* the triple [nat, 0, succ] *)

    mutable declared_nat: bool;

    decr: unit ID.Tbl.t;
      (* set of decreasing witnesses *)
  }

  type decode_state = state

  let create_state() = {
    map = ID.Tbl.create 32;
    nat_ty= {
      nat=ID.make "_nat";
      succ=ID.make "_succ";
      zero=ID.make "_zero";
    };
    decr = ID.Tbl.create 16;
    declared_nat=false;
  }

  let nat ~state = U.const state.nat_ty.nat
  let succ ~state x = U.app (U.const state.nat_ty.succ) [x]
  let zero ~state = U.const state.nat_ty.zero

  (* how to declare [nat] *)
  let declare_nat ~state =
    let ty_nat = nat ~state in
    let def = Stmt.mk_mutual_ty state.nat_ty.nat
        ~ty_vars:[]
        ~ty:U.ty_type
        ~cstors:
          [ state.nat_ty.zero, [], ty_nat
          ; state.nat_ty.succ, [ty_nat], U.ty_arrow ty_nat ty_nat]
    in
    Stmt.data ~info:Stmt.info_default [def]

  (* recursively traverse [t] and apply unrolled constants to
     their additional parameter. *)
  let rec rewrite_term ~state t =
    match T.repr t with
    | TI.Const id ->
        (* shall we unroll [id]? *)
        begin try
          let unroll = ID.Tbl.find state.map id in
          match unroll with
          | `Unroll id' -> U.app t [U.const id']
          | `Unroll_in_def t' -> U.app t [t']
        with Not_found -> t
        end
    | _ ->
        U.map () t
          ~bind:(fun () v -> (), v)
          ~f:(fun () t -> rewrite_term ~state t)

  (* get common polarity of all IDs in the list *)
  let polarity_of_list_ = function
    | [] -> assert false
    | id :: l ->
        let is_pos = match ID.polarity id with
          | Polarity.NoPol ->
              Utils.not_implemented "polarization is needed before unrolling"
          | Polarity.Pos -> true
          | Polarity.Neg -> false
        in
        (* check that all IDs have the same polarity *)
        assert
          (List.for_all
            (fun id' -> (if is_pos then Pol.is_pos else Pol.is_neg) (ID.polarity id'))
          l);
        is_pos

  (* make a variable for each type *)
  let make_vars tys =
    List.mapi (fun i ty -> Var.make ~name:(CCFormat.sprintf "v_%d" i) ~ty) tys

  (* replace [id]' polarized with [p] locally *)
  let with_local ~state id unroll ~f =
    ID.Tbl.add state.map id unroll;
    CCFun.finally
      ~h:(fun () -> ID.Tbl.remove state.map id)
      ~f

  (* unroll the list of predicates [l]. [v] is the variable used
     for unrolling *)
  let unroll_preds ~state v is_pos l =
    let open Stmt in
    (* translate one clause *)
    let tr_clause
      : type a. ID.t ->
        (term, term, a inv) Stmt.pred_clause ->
        (term, term, a inv) Stmt.pred_clause
      = fun id (Pred_clause c) ->
        Pred_clause {
          clause_vars = v :: c.clause_vars;
          clause_guard =
            (* in guard, replace [pred] by [pred v)] *)
            CCOpt.map
              (fun g -> rewrite_term ~state g)
              c.clause_guard;
          clause_concl =
            (* in concl, replace [pred] by [pred (Succ v)] *)
            let additional_param = succ ~state (U.var v) in
            with_local ~state id (`Unroll_in_def additional_param)
              ~f:(fun () -> rewrite_term ~state c.clause_concl);
        }
    in
    (* make new definitions for unrolled predicates *)
    List.map
      (fun def ->
        let d = def.Stmt.pred_defined in
        let id = d.Stmt.defined_head in
        (* modify the type of [id], add [nat_] as a first argument *)
        let defined =
          { d with
            defined_ty = U.ty_arrow (nat ~state) d.Stmt.defined_ty;
          } in
        (* translate the clauses *)
        let pred_clauses = List.map (tr_clause id) def.pred_clauses in
        (* if we unroll a coinductive predicate in negative polarity,
           we must add a base case [pred 0 _...._ = true].
           We don't need anything for an inductive predicate
           because [pred 0 _ = false] is the default semantic *)
        let pred_clauses =
          if is_pos then pred_clauses
          else (
            assert (ID.polarity id |> Pol.is_neg);
            let _, ty_args, _ = U.ty_unfold def.pred_defined.defined_ty in
            let vars = make_vars ty_args in
            let vars_t = List.map U.var vars in
            let c = Pred_clause {
              clause_vars = vars;
              clause_guard = None;
              clause_concl = U.app (U.const id) (zero ~state :: vars_t);
            } in
            c :: pred_clauses
          )
        in
        { def with
          pred_defined=defined;
          pred_clauses;
        })
      l

  (* translate non-well-founded predicates.
     Afterwards they will be well-founded. *)
  let define_preds ~state kind l =
    (* add a new variable of type nat, that will decrease from
       conclusion to guard *)
    let ids = List.map (fun def -> def.Stmt.pred_defined.Stmt.defined_head) l in
    let is_pos = polarity_of_list_ ids in
    match kind, is_pos with
      | `Pred, true
      | `Copred, false ->
          (* unroll the predicates *)
          Utils.debugf ~section 5
            "@[<2>unroll predicate(s)@ `@[%a@]`@]"
            (fun k->k PStmt.print_pred_defs l);
          let new_decls = ref [] in
          (* maybe we haven't declared [nat] yet *)
          if not state.declared_nat then (
            state.declared_nat <- true;
            new_decls := declare_nat ~state :: !new_decls;
          );
          let v = Var.make ~name:"_decr" ~ty:(nat ~state) in
          (* push the "regular" unrolling constants for each ID *)
          List.iter
            (fun id ->
              let n = ID.make (CCFormat.sprintf "decr_%a" ID.print_name id) in
              (* from now on, [id] will become [id n] *)
              ID.Tbl.add state.map id (`Unroll n);
              ID.Tbl.add state.decr n ();
              let st = Stmt.decl ~info:Stmt.info_default ~attrs:[] n (nat ~state) in
              new_decls := st :: !new_decls)
            ids;
          (* enter in "definition mode" for every defined predicate; locally
            the unrolling shall be done with [id v] *)
          List.iter
            (fun id -> ID.Tbl.add state.map id (`Unroll_in_def (U.var v)))
            ids;
          CCFun.finally
            ~f:(fun () ->
              let l = unroll_preds ~state v is_pos l in
              l, !new_decls)
            ~h:(fun () ->
              (* exit the definition mode *)
              List.iter (fun id -> ID.Tbl.remove state.map id) ids)
      | _ ->
          (* do not unroll *)
          let l = Stmt.map_preds ~term:(rewrite_term ~state) ~ty:CCFun.id l in
          l, []

  let tr_statement ~state st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Pred (`Not_wf, kind, l) ->
        (* translate the definitions, and obtain additional declarations *)
        let l, decls = define_preds ~state kind l in
        let st' = Stmt.mk_pred ~info ~wf:`Wf kind l in
        (* XXX: if the declaration of [nat] is in [decls], it is last,
           therefore using {!List.rev_append} here is important *)
        List.rev_append decls [st']
    | Stmt.Pred (`Wf, _, _)  (* keep, it's well founded *)
    | Stmt.Axiom _
    | Stmt.Copy _
    | Stmt.Decl _
    | Stmt.Goal _
    | Stmt.TyDef _ ->
        (* just rewrite terms to use the new unrolled predicates *)
        let st = Stmt.map st ~term:(rewrite_term ~state) ~ty:CCFun.id in
        [st]

  let unroll pb =
    let state = create_state () in
    let pb = Problem.flat_map_statements pb ~f:(tr_statement ~state) in
    pb, state

  (** {6 Decoding} *)

  module U_dt = Model.DT_util(T)

  (* rewrite the term recursively by removing the first argument to every
     term that is in the table *)
  let rec rewrite ~state t = match T.repr t with
    | TI.Const id ->
        assert (not (ID.Tbl.mem state.map id)); (* argument missing *)
        t
    | TI.App (f, l) ->
        begin match T.repr f, l with
        | _, [] -> assert false
        | TI.Const id, _ :: l' when ID.Tbl.mem state.map id ->
            (* [id] was unrolled, remove its first arg *)
            let l' = List.map (rewrite ~state) l' in
            U.app f l'
        | _ ->
            rewrite' ~state t
        end
    | _ -> rewrite' ~state t
  and rewrite' ~state t =
    U.map () t
      ~f:(fun () t -> rewrite ~state t)
      ~bind:(fun () v -> (), v)

      (* remove the tests for the unrolling variable in [dt] *)
  let filter_dt_ ~state ~removed_var dt =
    Utils.debugf ~section 5
      "@[<v>remove var @[%a@]@ from `@[%a@]`@]"
      (fun k->k Var.print_full removed_var (Model.DT.print P.print) dt);
    let tests =
      CCList.filter_map
        (fun (eqns, then_) ->
            let eqns' =
              CCList.filter_map
                (fun (v, t) ->
                  if Var.equal v removed_var
                  then None
                  else Some (v, rewrite ~state t))
                eqns
            in
            let then' = rewrite ~state then_ in
            Some (eqns', then'))
        dt.Model.DT.tests
    in
    let else_ = rewrite ~state dt.Model.DT.else_ in
    Model.DT.test tests ~else_

  (* remove the additional parameter introduced by unrolling, if any *)
  let decode_model ~state m =
    Model.filter_map m
      ~constants:(fun (t,u,k) ->
        match T.repr t with
        | TI.Const id
          when ID.equal id state.nat_ty.zero
            || ID.Tbl.mem state.decr id ->
            None (* remove "zero" and decreasing witnesses *)
        | _ ->
            let u = rewrite ~state u in
            Some (t,u,k))
      ~finite_types:(fun (t,dom) ->
        match T.repr t with
        | TI.Const id when ID.equal id state.nat_ty.nat ->
            None (* remove "nat" *)
        | _ -> Some (t,dom))
      ~funs:(fun (t,vars,dt,k) ->
        match T.repr t with
        | TI.Const id when ID.equal id state.nat_ty.succ ->
            None (* remove "succ" *)
        | TI.Const id when ID.Tbl.mem state.map id ->
            (* id is unrolled, remove the additional variable *)
            let removed_var, vars = match vars with
              | [] -> assert false
              | v :: l -> v, l
            in
            Utils.debugf ~section 5 "@[<2>remove var %a from DT of %a@]"
              (fun k->k Var.print_full removed_var ID.print id);
            let dt = filter_dt_ ~state ~removed_var dt in
            Some (t,vars,dt,k)
        | _ ->
            (* simply rewrite *)
            let dt = Model.DT.map dt ~term:(rewrite ~state) ~ty:CCFun.id in
            Some (t,vars,dt,k))

  (** {6 Pipes} *)

  let pipe_with ?(on_decoded) ~decode ~print ~check =
    let on_encoded =
      Utils.singleton_if print () ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after unrolling@}:@ %a@]@." Ppb.print)
      @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.check_problem ?env:None)
    in
    Transform.make1
      ?on_decoded
      ~name
      ~on_encoded
      ~encode:(fun pb -> unroll pb)
      ~decode
      ()

  let pipe ~print ~check =
    let on_decoded = if print
      then
        [Format.printf "@[<2>@{<Yellow>model after unrolling@}:@ %a@]@."
           (Model.print P.print P.print)]
      else []
    in
    pipe_with ~on_decoded ~decode:(fun state m -> decode_model ~state m)
      ~print ~check
end

