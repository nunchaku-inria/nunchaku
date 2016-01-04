
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates} *)

module TI = TermInner
module Stmt = Statement

type inv1 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Present]>
type inv2 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

let section = Utils.Section.make "elim_ind_pred"

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)

  type term = T.t
  type decode_state = unit

  (* transform a (co)inductive predicate into a recursive boolean function

     translate
     `forall y1_1 .. y1_m1, guard1 => id a1_1 .. a1_n;
      forall y2_1 .. y2_m2, guard2 => id a2_1 .. a2_n;
      ...`

     into
     `forall x1...xn,
         (exists y1_1...y1_m1, and_i (x_i = a1_i) && guard1)
         ||
         (exists y2_1...y2_m2, and_i (x_i = a2_i) && guard2)
         || ....`
  *)
  let pred_to_def
  : (term, term, inv1) Stmt.pred_def -> (term, term, inv2) Stmt.rec_def
  = fun pred ->
    Utils.debugf ~section 3 "@[<2>pred_to_def@ `@[%a@]`@]"
      (fun k->k PStmt.print_pred_def pred);
    assert (pred.Stmt.pred_tyvars = []); (* mono *)
    let d = pred.Stmt.pred_defined in
    let ty_vars, ty_args, ty_ret = U.ty_unfold d.Stmt.defined_ty in
    assert (U.ty_is_Prop ty_ret);
    assert (ty_vars = []); (* mono *)
    (* create new variables *)
    let vars =
      List.mapi
        (fun i ty ->
          let name = Format.sprintf "v_%d" i in
          Var.make ~name ~ty)
        ty_args
    in
    (* translate clauses into one existentially quantified case,
     then take the disjunction *)
    let cases =
      List.map
        (fun (Stmt.Pred_clause c) ->
          let case = c.Stmt.clause_concl in
          let case =
            CCOpt.maybe
              (fun g -> U.and_ [g; case])
              case
              c.Stmt.clause_guard
          in
          List.fold_right U.exists c.Stmt.clause_vars case)
        pred.Stmt.pred_clauses
    in
    let rhs = U.or_ cases in
    {Stmt.
      rec_defined=d;
      rec_kind=Stmt.Decl_prop;
      rec_vars=vars;
      rec_eqns=Stmt.Eqn_single (vars,rhs);
    }

  let elim_ind_preds
  : (term, term, inv1) Problem.t ->
    (term, term, inv2) Problem.t * decode_state
  = fun pb ->
    let pb' = Problem.flat_map_statements pb
      ~f:(fun st ->
          let info = Stmt.info st in
          match Stmt.view st with
          | Stmt.Pred (`Wf, _, l) ->
              (* well-founded: translate directly to recursive functions *)
              let l = List.map pred_to_def l in
              [Stmt.axiom_rec ~info l]
          | Stmt.Pred (`Not_wf, _, _) ->
              (* should have been  transformed into a [`Wf] (co)predicate
                 by polarize *)
              assert false
          | Stmt.Decl (id,k,d) -> [Stmt.mk_decl ~info id k d]
          | Stmt.Axiom (Stmt.Axiom_std l) -> [Stmt.axiom ~info l]
          | Stmt.Axiom (Stmt.Axiom_spec l) -> [Stmt.axiom_spec ~info l]
          | Stmt.Axiom (Stmt.Axiom_rec l) ->
              [Stmt.axiom_rec ~info (Stmt.cast_rec_defs l)]
          | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l]
          | Stmt.Goal g -> [Stmt.goal ~info g]
        )
    in
    pb', ()

  let decode_model ~state:_ m = m

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module Ppb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of inductive predicates:@ %a@]@." Ppb.print]
      else []
    in
    Transform.make1
      ~name:"elim_ind_pred"
      ~on_encoded
      ~encode:(fun pb -> elim_ind_preds pb)
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end
