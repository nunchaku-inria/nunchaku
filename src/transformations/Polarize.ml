
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Pol = Polarity
module Subst = Var.Subst
module T = Term
module PStmt = Stmt.Print(T)(T)

let name = "polarize"
let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "@[<2>in polarization:@ %s@]" msg)
      | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

type term = T.t

type polarized_id = {
  pos: ID.t;
  neg: ID.t;
}

type decode_state = (ID.t * bool * T.t * polarized_id) ID.Tbl.t
(* polarized_id -> (original_id, polarity, type, polarized_id) *)

let term_contains_undefined t =
  T.to_seq t
  |> Iter.exists
    (fun t' -> match T.repr t' with
       | TI.Builtin (`Undefined_self _) -> true
       | _ -> false)

(* does this set of equations contain an "undefined" sub-term? *)
let eqns_contains_undefined
  : (term, term) Stmt.equations -> bool
  = function
    | Stmt.Eqn_nested l ->
      List.exists
        (fun (_, args, rhs, side) ->
           List.exists term_contains_undefined args ||
           term_contains_undefined rhs ||
           List.exists term_contains_undefined side)
        l
    | Stmt.Eqn_app (_, _, lhs, rhs) ->
      term_contains_undefined lhs || term_contains_undefined rhs
    | Stmt.Eqn_single (_,rhs) ->
      term_contains_undefined rhs

type action =
  [ `Polarize of bool
  | `Keep (* do not polarize the symbol *)
  ]

let pp_act out = function
  | `Keep -> Format.fprintf out "keep"
  | `Polarize p -> Format.fprintf out "polarize(%B)" p

module St = struct
  type t = {
    polarized: polarized_id option ID.Tbl.t;
    (* id -> its polarized version, if we decided to polarize it *)

    polarize_rec: bool;
    (* enable/disable polarization of predicates defined with `rec` *)

    decode_state : decode_state;
    (* for decoding *)
  }

  let create ?(size=64) ~polarize_rec () =
    { polarized=ID.Tbl.create size;
      polarize_rec;
      decode_state = ID.Tbl.create 16;
    }
end

module Trav = Traversal.Make(T)(struct
    type t = action
    let equal = (=)
    let hash _ = 0
    let pp = pp_act
    let section = section
    let fail = errorf_
  end)(St)

(* shall we polarize the recursive function defined as follows? *)
let should_polarize_rec ~state def =
  state.St.polarize_rec (* option enabled? *)
  &&
  let _, ty_args, ty_ret = T.ty_unfold def.Stmt.rec_defined.Stmt.defined_ty in
  T.ty_is_Prop ty_ret
  &&
  List.length ty_args > 0 (* function, not constant *)
  &&
  not (eqns_contains_undefined def.Stmt.rec_eqns)

(* depending on polarity [pol], apply the proper id of [p] to
   arguments [l], along with guards [conds] *)
let app_polarized pol p l = match pol with
  | Pol.Pos -> T.app (T.const p.pos) l
  | Pol.Neg -> T.app (T.const p.neg) l
  | Pol.NoPol ->
    (* choose positive, but make both equal *)
    let p_pos = T.const p.pos and p_neg = T.const p.neg in
    let t = T.app p_pos l in
    (* force p_pos = p_neg here *)
    T.asserting t [ T.eq (T.app p_pos l) (T.app p_neg l) ]

(* return the pair of polarized IDs for [id], with caching *)
let polarize_id ~state ~ty id =
  assert (not (ID.Tbl.mem state.St.polarized id));
  let pos = ID.make_full ~needs_at:false ~pol:Pol.Pos (ID.name id) in
  let neg = ID.make_full ~needs_at:false ~pol:Pol.Neg (ID.name id) in
  let p = {pos; neg; } in
  ID.Tbl.add state.St.polarized id (Some p);
  (* reverse mapping, for decoding *)
  ID.Tbl.add state.St.decode_state pos (id, true, ty, p);
  ID.Tbl.add state.St.decode_state neg (id, false, ty, p);
  p

let find_polarized_exn ~state id =
  match ID.Tbl.find state.St.polarized id with
    | Some p -> p
    | None -> assert false

let polarize_def_of ~self id pol = match pol with
  | Pol.Pos -> Trav.call_dep self ~depth:0 id (`Polarize true)
  | Pol.Neg -> Trav.call_dep self ~depth:0 id (`Polarize false)
  | Pol.NoPol ->
    (* ask for both polarities *)
    Trav.call_dep self ~depth:0 id (`Polarize true);
    Trav.call_dep self ~depth:0 id (`Polarize false)

type subst = (T.t, T.t Var.t) Var.Subst.t

let is_prop ~self t =
  let ty = T.ty_exn ~env:(Trav.env self) t in
  T.ty_is_Prop ty

let returns_prop ~self t =
  let ty = T.ty_exn ~env:(Trav.env self) t in
  T.ty_returns_Prop ty

(* traverse [t], replacing some symbols by their polarized version,
   @return the term with more internal guards and polarized symbols *)
let rec polarize_term_rec
  : self:Trav.t -> Pol.t -> subst -> T.t -> T.t
  = fun ~self pol subst t ->
    let state = Trav.state self in
    (* how to polarize an ID whose type is/returns prop *)
    let maybe_polarize_const (id:ID.t) (ty:T.t) (l:T.t list) =
      if T.ty_is_Prop ty then (
        (* constant: degenerate case of (co)inductive pred, no need
                     for polarization, and necessarily WF. *)
        Utils.debugf ~section 5 "@[<2>do not polarize constant pred `%a`@]"
          (fun k->k ID.pp_full id);
        ID.Tbl.add state.St.polarized id None;
        Trav.call_dep self ~depth:0 id `Keep;
        assert (l = []);
        T.const id
      ) else (
        (* polarize *)
        Utils.debugf ~section 5 "@[<2>polarize pred `%a`@]"
          (fun k->k ID.pp_full id);
        polarize_def_of ~self id pol;
        let p = find_polarized_exn ~state id in
        app_polarized pol p l
      )
    and maybe_polarize_def (id:ID.t) (def:(_,_) Stmt.rec_def) (l:T.t list) =
      (* we can polarize, or not: delegate to heuristic *)
      if should_polarize_rec ~state def
      then (
        Utils.debugf ~section 5 "@[<2>polarize fun `%a`@]"
          (fun k->k ID.pp_full id);
        polarize_def_of ~self id pol;
        let p = find_polarized_exn ~state id in
        app_polarized pol p l
      ) else (
        Utils.debugf ~section 5 "@[<2>do not polarize fun `%a`@]"
          (fun k->k ID.pp_full id);
        ID.Tbl.add state.St.polarized id None;
        Trav.call_dep self ~depth:0 id `Keep;
        T.app_const id l
      )
    in
    match T.repr t with
      | TI.Builtin (`Guard (t, g)) ->
        let open Builtin in
        let g = {
          asserting = List.map (polarize_term_rec ~self Pol.Pos subst) g.asserting;
        } in
        let t = polarize_term_rec ~self pol subst t in
        T.guard t g
      | TI.Builtin (`True | `False | `DataTest _ | `Unparsable _
                   | `DataSelect _ | `Undefined_self _
                   | `Undefined_atom _ | `Card_at_least _) ->
        T.eval_renaming ~subst t
      | TI.Var v -> T.var (Var.Subst.find_exn ~subst v)
      | TI.Const id ->
        let info = Env.find_exn ~env:(Trav.env self) id in
        begin match Env.def info with
          | Env.Fun_def (_,def,_) ->
            maybe_polarize_def id def []
          | Env.Pred (_,_,_,_,_) ->
            let ty = Env.ty info in
            maybe_polarize_const id ty []
          | _ ->
            Trav.call_dep self ~depth:0 id `Keep; (* keep it as is *)
            t
        end
      | TI.App (f,l) ->
        let l = List.map (polarize_term_rec ~self Pol.NoPol subst) l in
        begin match T.repr f, l with
          | TI.Const id, _ when ID.Tbl.mem state.St.polarized id ->
            Utils.debugf ~section 5
              "@[<2>decision to polarize `%a` already taken@]"
              (fun k->k ID.pp_full id);
            (* we already chose whether [id] was polarized or not *)
            begin match ID.Tbl.find state.St.polarized id with
              | None ->
                Trav.call_dep self ~depth:0 id `Keep;
                T.app f l
              | Some p ->
                polarize_def_of ~self id pol;
                app_polarized pol p l
            end
          | TI.Const id, _ ->
            (* shall we polarize this constant? *)
            let info = Env.find_exn ~env:(Trav.env self) id in
            begin match Env.def info with
              | Env.NoDef
              | Env.Data (_,_,_)
              | Env.Cstor (_,_,_,_)
              | Env.Copy_abstract _
              | Env.Copy_concrete _
              | Env.Copy_ty _
              | Env.Fun_spec _ ->
                (* do not polarize *)
                ID.Tbl.add state.St.polarized id None;
                Trav.call_dep self ~depth:0 id `Keep;
                T.app f l
              | Env.Fun_def (_defs,def,_) ->
                maybe_polarize_def id def l
              | Env.Pred (_,_,pred,_preds,_) ->
                let d = pred.Stmt.pred_defined in
                maybe_polarize_const d.Stmt.defined_head d.Stmt.defined_ty l
            end
          | _ ->
            polarize_term_rec' ~self pol subst t
        end
      | TI.Bind (Binder.TyForall, _, _) ->
        T.eval_renaming ~subst t (* we do not polarize in types *)
      | TI.Builtin (`Eq (a,b)) when pol <> Pol.NoPol && is_prop ~self a ->
        (* we can gain precision here, because if we expand the <=> we
           obtain two polarized formulas, whereas if we keep it we
           only obtain a non-polarized one. *)
        polarize_term_rec ~self pol subst (T.and_ [T.imply a b; T.imply b a])
      | TI.Builtin (`Eq (a,b)) when returns_prop ~self a ->
        (* [f = g] when both are predicates ==>
           [f+ = g+ ∧ f- = g- asserting (f+=f- ∧ g+=g-)] *)
        let a_plus = polarize_term_rec ~self Pol.Pos subst a in
        let a_minus = polarize_term_rec ~self Pol.Neg subst a in
        let b_plus = polarize_term_rec ~self Pol.Pos subst b in
        let b_minus = polarize_term_rec ~self Pol.Neg subst b in
        T.asserting
          (T.and_ [T.eq a_plus b_plus; T.eq a_minus b_minus])
          [T.eq a_plus a_minus; T.eq b_plus b_minus]
      | TI.Bind ((Binder.Forall | Binder.Exists | Binder.Fun | Binder.Mu), _, _)
      | TI.Builtin (`Ite _ | `Eq _ | `And _ | `Or _ | `Not _  | `Imply _)
      | TI.Let _
      | TI.Match _ ->
        (* generic treatment *)
        polarize_term_rec' ~self pol subst t
      | TI.TyBuiltin _
      | TI.TyArrow (_,_) -> T.eval_renaming ~subst t
      | TI.TyMeta _ -> assert false

(* generic recursive step *)
and polarize_term_rec'
  : self:Trav.t -> Pol.t -> subst -> T.t -> T.t
  = fun ~self pol subst t ->
    T.map_pol subst pol t
      ~f:(fun subst pol -> polarize_term_rec ~self pol subst)
      ~bind:Subst.rename_var

(* [p] is the polarization of the function defined by [def]; *)
let define_rec
  : self:Trav.t -> bool ->
  (_, _) Stmt.rec_def ->
  polarized_id ->
  (_, _) Stmt.rec_def
  = fun ~self is_pos def p ->
    let open Stmt in
    let defined = def.rec_defined in
    let defined = { defined with defined_head=(if is_pos then p.pos else p.neg); } in
    Utils.debugf ~section 5 "@[<2>polarize def `@[%a@]`@ on %B@]"
      (fun k->k PStmt.pp_rec_def def is_pos);
    let pol = if is_pos then Pol.Pos else Pol.Neg in
    let rec_eqns =
      map_eqns_bind Var.Subst.empty pol def.rec_eqns
        ~bind:Subst.rename_var
        ~term:(fun subst pol -> polarize_term_rec ~self pol subst)
    in
    { def with
        rec_defined=defined;
        rec_eqns; }

(* [p] is the polarization of the predicate defined by [def]; *)
let define_pred
  : self:Trav.t ->
  is_pos:bool ->
  (_, _) Stmt.pred_def ->
  polarized_id ->
  (_, _) Stmt.pred_def
  = fun ~self ~is_pos def p ->
    let open Stmt in
    let defined = def.pred_defined in
    let defined =
      {defined
       with Stmt.
         defined_head=(if is_pos then p.pos else p.neg);
      }
    in
    let tr_clause
      : (term, term) pred_clause ->
        (term, term) pred_clause
      = fun clause ->
        let pol = if is_pos then Pol.Pos else Pol.Neg in
        (* we keep the same polarity in the conclusion and guard, because it is not
           a proper implication.
           Instead we see this as
           [concl <-> exists... guard] which, in positive polarity, will become
           [concl+ => exists... guard], making guard positive too *)
        map_clause_bind Var.Subst.empty clause
          ~bind:Subst.rename_var
          ~term:(fun subst _ -> polarize_term_rec ~self pol subst)
    in
    let pred_clauses = List.map tr_clause def.pred_clauses in
    { def with
        pred_defined=defined;
        pred_clauses; }

let polarize_term ~self subst pol t = polarize_term_rec ~self pol subst t

let dispatch = {
  Trav.

  do_term = (fun self ~depth:_ t ->
    polarize_term ~self Var.Subst.empty Pol.NoPol t
  );

  do_def = (fun self ~depth:_ def act ->
    let d = Stmt.defined_of_rec def in
    let id = Stmt.id_of_defined d in
    let ty = Stmt.ty_of_defined d in
    let st = Trav.state self in
    Utils.debugf ~section 5 "@[<2>polarize def `@[%a@]`@ on %a@]"
      (fun k->k ID.pp id pp_act act);
    match act with
      | `Keep ->
        ID.Tbl.replace st.St.polarized id None;
        let def =
          Stmt.map_rec_def_bind Var.Subst.empty def
            ~bind:Subst.rename_var
            ~ty:(fun _ ty -> ty)
            ~term:(polarize_term ~self) in
        def
      | `Polarize is_pos ->
        let p =
          try match ID.Tbl.find st.St.polarized id with
            | None -> assert false
            | Some p -> p
          with Not_found ->
            polarize_id ~state:st ~ty id
        in
        define_rec ~self is_pos def p
  );

  do_pred = (fun self ~depth:_ _wf _kind def act ->
    let d = Stmt.defined_of_pred def in
    let id = Stmt.id_of_defined d in
    let ty = Stmt.ty_of_defined d in
    let st = Trav.state self in
    if act<>`Keep
    then
      Utils.debugf ~section 2 "polarize (co)inductive predicate %a on (%a)"
        (fun k->k ID.pp id pp_act act);
    match act with
      | `Keep ->
        ID.Tbl.add st.St.polarized id None;
        let def =
          Stmt.map_pred_bind Var.Subst.empty def
            ~bind:Subst.rename_var ~ty:(fun _ ty -> ty)
            ~term:(fun subst pol -> polarize_term_rec ~self pol subst) in
        def
      | `Polarize is_pos ->
        let p =
          try
            match ID.Tbl.find st.St.polarized id with
              | None -> assert false (* incompatible *)
              | Some p -> p
          with Not_found -> polarize_id ~state:st ~ty id
        in
        define_pred ~self ~is_pos def p
  );

  (* goals, or axioms, start with positive polarity *)
  do_goal_or_axiom = Some (fun self ~depth:_ _ t ->
      polarize_term_rec ~self Pol.Pos Var.Subst.empty t
    );

  do_spec = None;

  do_copy = None;

  do_data = None;

  do_ty_def = None;
}

let polarize
  : polarize_rec:bool ->
  (term, term) Problem.t ->
  (term, term) Problem.t * decode_state
  = fun ~polarize_rec pb ->
    let state = St.create ~polarize_rec () in
    let trav =
      Trav.create
        ~env:(Env.create())
        ~dispatch
        ~state
        ()
    in
    Problem.iter_statements pb ~f:(Trav.traverse_stmt trav);
    let res = Trav.get_statements trav in
    let pb' =
      Problem.make (CCVector.freeze res)
        ~meta:(Problem.metadata pb)
    in
    pb', state.St.decode_state

(** {6 Decoding} *)

module M = Model
module DT = M.DT
module DTU = Model.DT_util

type rw_sys = ID.t ID.Map.t

(* rewrite the term recursively.
   Rules are of the form [id -> id'], meaning [id] should
   be rewritten into [id']
*)
let rec rewrite ~subst (sys:rw_sys) t =
  match T.repr t with
    | TI.Var v -> T.var (Subst.deref_rec ~subst v)
    | TI.Const id ->
      begin try
          let id' = ID.Map.find id sys in
          T.const id'
        with Not_found -> t
      end
    | TI.App (f, l) ->
      begin match T.repr f with
        | TI.Const id ->
          begin try
              let id' = ID.Map.find id sys in
              let l = List.map (rewrite ~subst sys) l in
              T.app (T.const id') l
            with Not_found ->
              rewrite' ~subst sys t
          end
        | _ -> rewrite' ~subst sys t
      end
    | _ -> t
and rewrite' ~subst sys t =
  T.map subst t
    ~f:(fun subst t -> rewrite ~subst sys t)
    ~bind:(fun s v -> s, v)

let find_polarized_ ~(state:decode_state) id =
  try ID.Tbl.find state id
  with Not_found ->
    errorf_ "could not find polarized symbol `%a` when decoding" ID.pp id

(* build a rewrite system from the given model. The rewrite system erases
   polarized IDs into their non-polarized version. *)
let make_rw_sys_ ~state m : rw_sys =
  Model.fold ID.Map.empty m
    ~finite_types:(fun sys _ -> sys)
    ~values:(fun sys (t,_,_) -> match T.repr t with
      | TI.Const id when ID.is_polarized id ->
        (* rewrite into the unpolarized version *)
        let id', _is_pos, _, _p = find_polarized_ ~state id in
        Utils.debugf ~section 4 "@[<2>decoding:@ rewrite %a into %a@]"
          (fun k->k ID.pp id ID.pp id');
        ID.Map.add id id' sys
      | _ -> sys)

let rewrite_dt ~sys dt : (_,_) DT.t =
  DT.map dt
    ~term:(rewrite ~subst:Subst.empty sys)
    ~ty:CCFun.id

let rec is_undefined_ t = match T.repr t with
  | TI.Builtin (`Undefined_atom _ | `Undefined_self _) -> true
  | TI.App (f, _) -> is_undefined_ f
  | _ -> false

(* filter [dt], the decision tree for [polarized], returning
   only the cases that return [true] (if [is_pos]) or [false] (if [not is_pos]) *)
let filter_dt_ ~polarized ~default:d dt : (_,_) DT.t =
  let is_pos = ID.is_pos polarized in
  Utils.debugf ~section 5
    "@[<v>retain branches that yield %B for `%a`@ from `@[%a@]`@]"
    (fun k->k is_pos ID.pp polarized (Model.DT.pp T.pp' T.pp) dt);
  let rec aux dt : _ option = match dt with
    | DT.Yield t ->
      (* evaluate as fully as possible, hoping for [true] or [false] *)
      let t = T.Red.whnf t in
      begin match T.repr t, is_pos with
        | TI.Builtin `True, true
        | TI.Builtin `False, false -> Some (DT.yield t)
        | TI.Builtin `False, true
        | TI.Builtin `True, false -> None
        | _ when is_undefined_ t ->
          None (* undefined case, we drop, it will be added back later *)
        | _ ->
          errorf_
            "@[<2>expected decision tree for %a@ to yield only true/false@ \
             but branch `@[%a@]`@ yields `@[%a@]`@]"
            ID.pp polarized DTU.pp dt T.pp t
      end
    | DT.Cases {DT.var; tests=DT.Tests l; default} ->
      let l =
        CCList.filter_map
          (fun (lhs,rhs) -> match aux rhs with
             | None -> None
             | Some rhs' -> Some (lhs, rhs'))
          l
      and default =
        CCOpt.flat_map aux default
      in
      if l=[] && default=None
      then None (* empty *)
      else Some (DT.mk_tests var ~tests:l ~default)
    | DT.Cases {DT.var; tests=DT.Match (m,missing); default} ->
      let new_m, new_missing =
        ID.Map.fold
          (fun id (tys, vars,rhs) (new_m,new_missing) ->
             match aux rhs with
               | None ->
                 (* remove! *)
                 new_m, ID.Map.add id (List.length vars) new_missing
               | Some rhs ->
                 ID.Map.add id (tys,vars,rhs) new_m, new_missing)
          m
          (ID.Map.empty, missing)
      and default =
        CCOpt.flat_map aux default
      in
      if ID.Map.is_empty new_m && CCOpt.is_none default
      then None
      else Some (DT.mk_match var ~by_cstor:new_m ~missing:new_missing ~default)
  in
  CCOpt.get_lazy
    (fun () -> DT.const (DT.vars dt) (DT.yield d))
    (aux dt)

(* decoding:
   - keep positive cases for p+, negative cases for p-, and undefined otherwise
*)
let decode_model ~state m =
  (* compute a rewrite system for eliminating polarized IDs *)
  let sys = make_rw_sys_ ~state m in
  (* this tables stores the half-decision tree for polarized IDs
     (when we have met one polarity but not the other, and we know the other
     is defined somewhere in the model) *)
  let partial_map : (_,_) DT.t ID.Tbl.t = ID.Tbl.create 32 in
  Model.filter_map m
    ~finite_types:(fun (t,dom) -> Some (t,dom))
    ~values:(fun (t,dt,k) -> match T.repr t with
      | TI.Const id when ID.is_polarized id ->
        (* unpolarize. id' is the unpolarized ID. *)
        let id_non_pol, is_pos, ty, p = find_polarized_ ~state id in
        let opp_id = if is_pos then p.neg else p.pos in
        begin match ID.Tbl.get partial_map id_non_pol with
          | Some dt' ->
            (* if [id' in partial_map], we already met its other polarized
               version, so we can merge the decision trees and push [id']
               in the model. *)
            let vars' = DT.vars dt' in
            (* use the same variables for both halves of DT *)
            let vars = DT.vars dt in
            let subst = Subst.of_list vars vars' in
            let dt = DTU.map_vars ~subst dt in
            let default = T.app (T.undefined_atom ~ty) (List.map T.var vars') in
            (* only keep branches that return true/false (depending on pol) *)
            let dt =
              filter_dt_ ~polarized:id ~default dt
              |> rewrite_dt ~sys
            and dt' =
              filter_dt_ ~polarized:opp_id ~default dt'
              |> rewrite_dt ~sys
            in
            (* merge the two partial decision trees — they should not overlap *)
            let new_dt = DTU.merge dt dt' in
            (* add default case *)
            let new_dt = DT.add_default default new_dt in
            (* emit model for [id'] *)
            Some (T.const id_non_pol, new_dt, k)
          | None ->
            if ID.Map.mem opp_id sys
            then (
              (* store the decision tree in [partial_map]; [id'] will
                 be added to the model when its second polarized version
                 is met *)
              ID.Tbl.add partial_map id_non_pol dt;
              None
            ) else (
              (* the other polarized version of [id'] is not defined in the
                 model, we can emit this function now *)
              let default =
                let vars = DT.vars dt in
                T.app (T.undefined_atom ~ty) (List.map T.var vars)
              in
              let new_dt =
                filter_dt_ ~polarized:id ~default dt
                |> rewrite_dt ~sys
              in
              (* add default case *)
              let new_dt = DT.add_default default new_dt in
              Some (T.const id_non_pol, new_dt, k)
            )
        end
      | _ ->
        (* rewrite polarized IDs *)
        let t = rewrite ~subst:Subst.empty sys t in
        let dt = rewrite_dt ~sys dt in
        Some (t,dt,k))

(** {6 Pipes} *)

let pipe_with ?on_decoded ~decode ~polarize_rec ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.P in
      Format.printf "@[<v2>@{<Yellow>after polarization@}:@ %a@]@." Ppb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono; Ind_preds, Present])
    ~on_encoded ?on_decoded
    ~encode:(fun pb -> polarize ~polarize_rec pb)
    ~decode
    ()

let pipe ~polarize_rec ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after polarize@}:@ %a@]@."
         (Problem.Res.pp T.pp' T.pp)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model ~state) in
  pipe_with ~decode ~on_decoded ~polarize_rec ~print ~check

