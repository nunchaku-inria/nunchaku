
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Polarize} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Pol = Polarity
module Subst = Var.Subst
module T = TI.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)
module Red = Reduce.Make(T)

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds:[`Present]>

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

type 'a env = (term, term, 'a inv) Env.t

type polarized_id = {
  pos: ID.t;
  neg: ID.t;
}

type decode_state = (ID.t * bool * polarized_id) ID.Tbl.t
    (* polarized_id -> (original_id, polarity, polarized_id) *)

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

    decode_state : decode_state;
      (* for decoding *)

    mutable call: depth:int -> ID.t -> action -> unit;
      (* callback for recursion *)

    mutable get_env: unit -> 'a env;

    mutable add_deps : ID.t -> unit;
  }

  let create ?(size=64) ~polarize_rec () =
    { polarized=ID.Tbl.create size;
      polarize_rec;
      decode_state = ID.Tbl.create 16;
      call=(fun ~depth:_ _ _ -> assert false);
      get_env=(fun () -> assert false);
      add_deps=(fun _ -> assert false);
  }
  let env ~state = state.get_env()
  let call ~state ~depth id pol = state.call ~depth id pol
end

(* shall we polarize the recursive function defined as follows? *)
let should_polarize_rec ~state def =
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
let app_polarized pol p l = match pol with
  | Pol.Pos -> U.app (U.const p.pos) l
  | Pol.Neg -> U.app (U.const p.neg) l
  | Pol.NoPol ->
    (* choose positive, but make both equal *)
    let p_pos = U.const p.pos and p_neg = U.const p.neg in
    let t = U.app p_pos l in
    (* force p_pos = p_neg here *)
    U.asserting t [ U.eq (U.app p_pos l) (U.app p_neg l) ]

(* return the pair of polarized IDs for [id], with caching *)
let polarize_id ~state id =
  assert (not (ID.Tbl.mem state.St.polarized id));
  let pos = ID.make_full ~needs_at:false ~pol:Pol.Pos (ID.name id) in
  let neg = ID.make_full ~needs_at:false ~pol:Pol.Neg (ID.name id) in
  let p = {pos; neg; } in
  ID.Tbl.add state.St.polarized id (Some p);
  (* reverse mapping, for decoding *)
  ID.Tbl.add state.St.decode_state pos (id, true, p);
  ID.Tbl.add state.St.decode_state neg (id, false, p);
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

type subst = (T.t, T.t Var.t) Var.Subst.t

let is_prop ~state t =
  let ty = U.ty_exn ~sigma:(Env.find_ty ~env:(St.env ~state)) t in
  U.ty_is_Prop ty

(* traverse [t], replacing some symbols by their polarized version,
   @return the term with more internal guards and polarized symbols *)
let rec polarize_term_rec
: type i. state:i St.t -> Pol.t -> subst -> T.t -> T.t
= fun ~state pol subst t ->
  match T.repr t with
  | TI.Builtin (`Guard (t, g)) ->
      let open TI.Builtin in
      let g = {
        asserting = List.map (polarize_term_rec ~state Pol.Pos subst) g.asserting;
        assuming = List.map (polarize_term_rec ~state Pol.Neg subst) g.assuming;
      } in
      let t = polarize_term_rec ~state pol subst t in
      U.guard t g
  | TI.Builtin (`True | `False | `DataTest _ | `Unparsable _
               | `DataSelect _ | `Undefined _) ->
      U.eval_renaming ~subst t
  | TI.Var v -> U.var (Var.Subst.find_exn ~subst v)
  | TI.Const id ->
      St.call ~state ~depth:0 id `Keep; (* keep it as is *)
      t
  | TI.App (f,l) ->
      let l = List.map (polarize_term_rec ~state Pol.NoPol subst) l in
      begin match T.repr f, l with
      | TI.Const id, _ when ID.Tbl.mem state.St.polarized id ->
          Utils.debugf ~section 5
            "@[<2>decision to polarize `%a` already taken@]"
            (fun k->k ID.print_full id);
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
          | Env.Copy_abstract _
          | Env.Copy_concrete _
          | Env.Copy_ty _
          | Env.Fun_spec _ ->
              (* do not polarize *)
              ID.Tbl.add state.St.polarized id None;
              St.call ~state ~depth:0 id `Keep;
              U.app f l
          | Env.Fun_def (_defs,def,_) ->
              (* we can polarize, or not: delegate to heuristic *)
              if should_polarize_rec ~state def
              then (
                Utils.debugf ~section 5 "@[<2>polarize fun `%a`@]"
                  (fun k->k ID.print_full id);
                polarize_def_of ~state id pol;
                let p = find_polarized_exn ~state id in
                app_polarized pol p l
              ) else (
                Utils.debugf ~section 5 "@[<2>do not polarize fun `%a`@]"
                  (fun k->k ID.print_full id);
                ID.Tbl.add state.St.polarized id None;
                St.call ~state ~depth:0 id `Keep;
                U.app f l
              )
          | Env.Pred (_,_,pred,_preds,_) ->
              let ty = pred.Stmt.pred_defined.Stmt.defined_ty in
              if U.ty_is_Prop ty then (
                (* constant: degenerate case of (co)inductive pred, no need
                   for polarization, and necessarily WF. *)
                Utils.debugf ~section 5 "@[<2>do not polarize pred `%a`@]"
                  (fun k->k ID.print_full id);
                ID.Tbl.add state.St.polarized id None;
                St.call ~state ~depth:0 id `Keep;
                assert (l = []);
                f
              ) else (
                (* polarize *)
                Utils.debugf ~section 5 "@[<2>polarize pred `%a`@]"
                  (fun k->k ID.print_full id);
                polarize_def_of ~state id pol;
                let p = find_polarized_exn ~state id in
                app_polarized pol p l
              )
          end
      | _ ->
          polarize_term_rec' ~state pol subst t
      end
  | TI.Bind (`TyForall, _, _) ->
      U.eval_renaming ~subst t (* we do not polarize in types *)
  | TI.Builtin (`Eq (a,b)) when pol <> Pol.NoPol && is_prop ~state a ->
      (* we can gain precision here, because if we expand the <=> we
        obtain two polarized formulas, whereas if we keep it we
        only obtain a non-polarized one. *)
      polarize_term_rec ~state pol subst (U.and_ [U.imply a b; U.imply b a])
  | TI.Bind ((`Forall | `Exists | `Fun | `Mu), _, _)
  | TI.Builtin (`Ite _ | `Eq _ | `And _ | `Or _ | `Not _  | `Imply _)
  | TI.Let _
  | TI.Match _ ->
      (* generic treatment *)
      polarize_term_rec' ~state pol subst t
  | TI.TyBuiltin _
  | TI.TyArrow (_,_) -> U.eval_renaming ~subst t
  | TI.TyMeta _ -> assert false

(* generic recursive step *)
and polarize_term_rec'
: type i. state:i St.t -> Pol.t -> subst -> T.t -> T.t
= fun ~state pol subst t ->
  U.map_pol subst pol t
    ~f:(fun subst pol -> polarize_term_rec ~state pol subst)
    ~bind:Subst.rename_var

(* [p] is the polarization of the function defined by [def]; *)
let define_rec
: type a.
  state:a St.t -> bool ->
  (_, _, a inv) Stmt.rec_def ->
  polarized_id ->
  (_, _, a inv) Stmt.rec_def
= fun ~state is_pos def p ->
  let open Stmt in
  let defined = def.rec_defined in
  let defined = { defined with defined_head=(if is_pos then p.pos else p.neg); } in
  Utils.debugf ~section 5 "@[<2>polarize def `@[%a@]`@ on %B@]"
    (fun k->k PStmt.print_rec_def def is_pos);
  let rec_eqns = map_eqns_bind Var.Subst.empty def.rec_eqns
    ~bind:Subst.rename_var
    ~term:(polarize_term_rec ~state (if is_pos then Pol.Pos else Pol.Neg))
  in
  { def with
    rec_defined=defined;
    rec_eqns; }

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
  let defined =
    { Stmt.
      defined_head=(if is_pos then p.pos else p.neg);
      defined_ty=defined.Stmt.defined_ty;
    } in
  let tr_clause
    : type a.
        (term, term, a inv) pred_clause ->
        (term, term, a inv) pred_clause
    = fun clause ->
      let pol = if is_pos then Pol.Pos else Pol.Neg in
      (* we keep the same polarity in the guard, because it is not
         a proper implication. Instead we see this as
         [concl <-> exists... guard] which, in positive polarity, will become
         [concl+ => exists... guard], making guard positive too *)
      map_clause_bind Var.Subst.empty clause
        ~bind:Subst.rename_var ~term:(polarize_term_rec ~state pol)
  in
  let pred_clauses = List.map tr_clause def.pred_clauses in
  { def with
    pred_defined=defined;
    pred_clauses; }

let polarize_term ~state subst t = polarize_term_rec ~state Pol.NoPol subst t

let conf = {Traversal.
  direct_tydef=true;
  direct_spec=true;
  direct_copy=true;
  direct_mutual_types=true;
}

class ['a, 'c] traverse_pol ?(size=64) ~polarize_rec () = object(self)
  inherit ['a inv, 'a inv, 'c] Trav.traverse ~conf ~size ()

  val st: 'inv1 St.t = St.create ~polarize_rec ()

  method setup() =
    st.St.call <- self#do_statements_for_id;
    st.St.get_env <- (fun () -> self#env);
    ()

  method decode_state = st.St.decode_state

  method do_def ~depth:_ def act =
    let id = def.Stmt.rec_defined.Stmt.defined_head in
    Utils.debugf ~section 5 "@[<2>polarize def `@[%a@]`@ on %a@]"
      (fun k->k ID.print id pp_act act);
    match act with
    | `Keep ->
        ID.Tbl.replace st.St.polarized id None;
        let def =
          Stmt.map_rec_def_bind Var.Subst.empty def
            ~bind:Subst.rename_var
            ~ty:(fun _ ty -> ty)
            ~term:(polarize_term ~state:st) in
        [def]
    | `Polarize is_pos ->
        let p =
          try match ID.Tbl.find st.St.polarized id with
            | None -> assert false
            | Some p -> p
          with Not_found ->
            polarize_id ~state:st id
        in
        [define_rec ~state:st is_pos def p]

  method do_pred ~depth:_ _wf _kind def act =
    let id = def.Stmt.pred_defined.Stmt.defined_head in
    if act<>`Keep
    then
      Utils.debugf ~section 2 "polarize (co)inductive predicate %a on (%a)"
       (fun k->k ID.print id pp_act act);
    match act with
    | `Keep ->
        ID.Tbl.add st.St.polarized id None;
        let def =
          Stmt.map_pred_bind Var.Subst.empty def
            ~bind:Subst.rename_var ~ty:(fun _ ty -> ty)
            ~term:(polarize_term_rec ~state:st Pol.Pos) in
        [def]
    | `Polarize is_pos ->
        let p =
          try
            match ID.Tbl.find st.St.polarized id with
            | None -> assert false (* incompatible *)
            | Some p -> p
          with Not_found -> polarize_id ~state:st id
        in
        [define_pred ~state:st ~is_pos def p]

  method do_term ~depth:_ t = polarize_term ~state:st Var.Subst.empty t

  method! do_goal_or_axiom _ t = polarize_term_rec ~state:st Pol.Pos Var.Subst.empty t

  method do_spec ~depth:_ ~loc:_ _ _ = assert false

  method do_copy ~depth:_ ~loc:_ _ _ = assert false

  method do_mutual_types ~depth:_ _ _ = assert false

  method do_ty_def ?loc:_ ~attrs:_ _ ~ty:_ _ = assert false
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
   Rules are of the form [id -> id'], meaning [id] should
   be rewritten into [id']
  *)
let rec rewrite ~subst sys t =
  match T.repr t with
  | TI.Var v -> U.var (Subst.deref_rec ~subst v)
  | TI.Const id ->
      begin try
        let id' = ID.Map.find id sys in
        U.const id'
      with Not_found -> t
      end
  | TI.App (f, l) ->
      begin match T.repr f with
      | TI.Const id ->
          begin try
            let id' = ID.Map.find id sys in
            let l = List.map (rewrite ~subst sys) l in
            U.app (U.const id') l
          with Not_found ->
            rewrite' ~subst sys t
          end
      | _ -> rewrite' ~subst sys t
      end
  | _ -> t
and rewrite' ~subst sys t =
  U.map subst t
    ~f:(fun subst t -> rewrite ~subst sys t)
    ~bind:(fun s v -> s, v)

(* filter [dt], the decision tree for [polarized], returning
   only the cases that return [true] (if [is_pos]) or [false] (if [not is_pos]) *)
let filter_dt_ ~is_pos ~polarized ~sys ~subst dt =
  Utils.debugf ~section 5
    "@[<v>retain branches that yield %B for `%a`@ from `@[%a@]`@]"
    (fun k->k is_pos ID.print polarized (Model.DT.print P.print) dt);
  CCList.filter_map
    (fun (eqns, then_) ->
      (* evaluate as fully as possible, hoping for [true] or [false] *)
      let then_ = Red.whnf then_ in
      match T.repr then_, is_pos with
      | TI.Builtin `True, true
      | TI.Builtin `False, false ->
          let eqns' =
            CCList.map
              (fun (v, t) -> Subst.deref_rec ~subst v, rewrite ~subst sys t)
              eqns
          in
          let then' = rewrite ~subst sys then_ in
          Some (eqns', then')
      | TI.Builtin `False, true
      | TI.Builtin `True, false -> None
      | _ ->
          errorf_
            "@[<2>expected decision tree for %a@ to yield only true/false@ \
             but branch `@[%a@]`@ yields `@[%a@]`@]"
             ID.print polarized (Model.DT.print_tests P.print) eqns P.print then_)
    dt.Model.DT.tests

let find_polarized_ ~state id =
  try ID.Tbl.find state id
  with Not_found ->
    errorf_ "could not find polarized symbol `%a` when decoding" ID.print id

(* build a rewrite system from the given model. The rewrite system erases
   polarities and unrolling parameters.

   NOTE: this rewrite system is also useful for knowing whether a
   particular polarized symbol occurs in the model or not. *)
let make_rw_sys_ ~state m =
  Model.fold ID.Map.empty m
    ~constants:(fun sys _ -> sys)
    ~finite_types:(fun sys _ -> sys)
    ~funs:(fun sys (t,_,_,_) ->
      match T.repr t with
      | TI.Const id when ID.is_polarized id ->
          (* rewrite into the unpolarized version *)
          let id', _is_pos, _p = find_polarized_ ~state id in
          Utils.debugf ~section 4 "@[<2>decoding:@ rewrite %a into %a@]"
            (fun k->k ID.print id ID.print id');
          ID.Map.add id id' sys
      | _ -> sys)

(* decoding:
  - keep positive cases for p+, negative cases for p-, and undefined otherwise
  - remove the additional parameter introduced by unrolling, if any
*)
let decode_model ~state m =
  (* compute a rewrite system for eliminating polarized IDs *)
  let sys = make_rw_sys_ ~state m in
  (* this tables stores the half-decision tree for polarized IDs
     (when we have met one polarity but not the other, and we know the other
     is defined somewhere in the model) *)
  let partial_map = ID.Tbl.create 32 in
  Model.filter_map m
    ~constants:(fun (t,u,k) ->
          let u = rewrite ~subst:Subst.empty sys u in
          Some (t,u,k))
    ~finite_types:(fun (t,dom) -> Some (t,dom))
    ~funs:(fun (t,vars,dt,k) ->
      match T.repr t with
      | TI.Const id when ID.is_polarized id ->
          (* unpolarize. id' is the unpolarized ID. *)
          let id', is_pos, p = find_polarized_ ~state id in
          begin try
            (* if [id' in partial_map], we already met its other polarized
               version, so we can merge the decision trees and push [id']
               in the model. *)
            let vars', cases' = ID.Tbl.find partial_map id' in
            (* use the same variables for both halves of DT *)
            let subst = Subst.add_list ~subst:Subst.empty vars vars' in
            let cases = filter_dt_ ~polarized:id ~is_pos ~sys ~subst dt in
            (* merge the two partial decision trees — they should not overlap *)
            let else_ = U.undefined_ (U.app (U.const id') (List.map U.var vars')) in
            let new_dt =
              Model.DT.test
                (List.rev_append cases cases')
                ~else_
            in
            (* emit model for [id'] *)
            Some (U.const id', vars', new_dt, k)
          with Not_found ->
            let opp_id = if is_pos then p.neg else p.pos in
            let cases = filter_dt_ ~polarized:id ~is_pos ~sys ~subst:Subst.empty dt in
            if ID.Map.mem opp_id sys
            then (
              (* store the decision tree in [partial_map]; [id'] will
                 be added to the model when its second polarized version
                 is met *)
              ID.Tbl.add partial_map id' (vars,cases);
              None
            ) else (
              (* the other polarized version of [id'] is not defined in the
                 model, we can emit this function now *)
              let else_ = U.undefined_ (U.app (U.const id') (List.map U.var vars)) in
              let new_dt = Model.DT.test cases ~else_ in
              Some (U.const id', vars, new_dt, k)
            )
          end
      | _ ->
          (* remove polarized IDs *)
          let dt = Model.DT.map dt
            ~term:(rewrite ~subst:Subst.empty sys)
            ~ty:CCFun.id in
          Some (t,vars,dt,k))

(** {6 Pipes} *)

let pipe_with ?on_decoded ~decode ~polarize_rec ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after polarization@}:@ %a@]@." Ppb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.check_problem ?env:None)
  in
  Transform.make
    ~name
    ~on_encoded ?on_decoded
    ~encode:(fun pb -> polarize ~polarize_rec pb)
    ~decode
    ()

let pipe ~polarize_rec ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after polarize@}:@ %a@]@."
         (Problem.Res.print P.print P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model ~state) in
  pipe_with ~decode ~on_decoded ~polarize_rec ~print ~check

