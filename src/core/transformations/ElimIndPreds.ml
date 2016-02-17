
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates} *)

module TI = TermInner
module Stmt = Statement

type inv1 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Present]>
type inv2 = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

let name = "elim_ind_pred"

let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some (CCFormat.sprintf "@[<2>error in elim_ind_pred:@ %s@]" msg)
    | _ -> None)

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)

  type term = T.t
  type decode_state = unit

  let error_ msg = raise (Error msg)
  let errorf_ msg = CCFormat.ksprintf msg ~f:error_

  exception ExitAsCstors

  (* if [t = c1(c2_1(...), c2_2(...), ...)] recursively, where each [c_] is
     a (co)data constructor and leaves are variables, then it returns
     [Some (conds, subst')] where:
       - [conds] is a set of conditions for [t] to have the given shape
       - [subst'] is an extension of [subst] that binds leave variables
         to selectors on [t]
    @param env environment
    @param root the term that must have the shaped described by [t]
  *)
  let as_cstors ~env ~subst ~root t =
    let subst = ref subst in
    let conds = ref [] in
    let rec aux select t = match T.repr t with
      | TI.Var v ->
          begin match Var.Subst.find ~subst:!subst v with
          | None ->
              (* bind [v] *)
              subst := Var.Subst.add ~subst:!subst v select
          | Some select' ->
              (* [v = select] and [v = select'], so we better make sure
                 that [select = select'] to eliminate [v] *)
              conds := U.eq select select' :: !conds
          end
      | TI.App (f, l) ->
          begin match T.repr f with
          | TI.Const id ->
              let info = Env.find_exn ~env id in
              begin match Env.def info with
              | Env.Cstor _ ->
                  (* yay, a constructor!
                    - ensure that [select] has this constructor as head
                    - transform each subterm in [l] *)
                  conds := U.data_test id select :: !conds;
                  List.iteri
                    (fun i t' -> aux (U.data_select id i select) t')
                    l
              | _ -> raise ExitAsCstors
              end
          | _ -> raise ExitAsCstors
          end
      | _ -> raise ExitAsCstors
    in
    try
      aux root t;
      Some (!subst, !conds)
    with ExitAsCstors -> None

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
  : env:(term, term, inv1) Env.t ->
    (term, term, inv1) Stmt.pred_def ->
    (term, term, inv2) Stmt.rec_def
  = fun ~env pred ->
    Utils.debugf ~section 3 "@[<2>pred_to_def@ `@[%a@]`@]"
      (fun k->k PStmt.print_pred_def pred);
    assert (pred.Stmt.pred_tyvars = []); (* mono *)
    let d = pred.Stmt.pred_defined in
    let id = d.Stmt.defined_head in
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
    let arity = List.length ty_args in
    (* translate clauses into one existentially quantified case,
     then take the disjunction *)
    let cases =
      List.map
        (fun (Stmt.Pred_clause c) ->
          (* the clause should be [guard => id args], here we extract [args] *)
          let args =
            let fail() =
              errorf_
                "@[<2>expect conclusion of clause to be of the \
                form@ `%a <arg_1...arg_%d>`,@ but got `@[%a@]`@]"
                ID.print id arity P.print c.Stmt.clause_concl
            in
            match T.repr c.Stmt.clause_concl with
            | TI.App (f, l) ->
                if List.length l <> arity then fail();
                begin match T.repr f with
                | TI.Const id' when ID.equal id' id -> l
                | _ -> fail()
                end
            | _ -> fail()
          in
          (* add conditions that enforce [vargs = args].
             For optimization purpose, we replace
               `∃ y, x=s (s y) && p[y]`
               with
               `is-succ x && is-succ (pred x) && p[pred (pred x)]` *)
          let subst, conds =
            List.fold_left2
              (fun (subst,l) v arg ->
                match T.repr arg with
                | TI.Var v' ->
                    (* [arg_i = v'], so making [arg_i = v] is as simple as [v' := v] *)
                    Var.Subst.add ~subst v' (U.var v), l
                | _ ->
                    begin match as_cstors ~env ~subst arg ~root:(U.var v) with
                    | Some (subst', conds) ->
                        subst', conds @ l
                    | None ->
                        (* default: just add constraint [arg_i = v] *)
                        subst, U.eq (U.var v) arg :: l
                    end)
              (Var.Subst.empty, [])
              vars args
          in
          let conds = List.rev_map (U.eval ~subst) conds in
          (* add guard, if any *)
          let res = match c.Stmt.clause_guard with
            | None -> U.and_ conds
            | Some g -> U.and_ (U.eval ~subst g :: conds)
          in
          (* quantify over the clause's variables that are not eliminated *)
          let cvars =
            List.filter
              (fun v -> not (Var.Subst.mem ~subst v))
              c.Stmt.clause_vars in
          List.fold_right U.exists cvars res)
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
    let env = Problem.env pb in
    let pb' = Problem.flat_map_statements pb
      ~f:(fun st ->
          let info = Stmt.info st in
          match Stmt.view st with
          | Stmt.Pred (`Wf, _, l) ->
              (* well-founded: translate directly to recursive functions *)
              let l = List.map (pred_to_def ~env) l in
              [Stmt.axiom_rec ~info l]
          | Stmt.Pred (`Not_wf, _, _) ->
              (* should have been  transformed into a [`Wf] (co)predicate
                 by polarize *)
              Utils.not_implemented
                "cannot eliminate non-well-founded predicates without polarization"
          | Stmt.Decl (id,k,d,attrs) -> [Stmt.mk_decl ~info ~attrs id k d]
          | Stmt.Copy c -> [Stmt.copy ~info c]
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
      ~name
      ~on_encoded
      ~encode:(fun pb -> elim_ind_preds pb)
      ~decode
      ()

  let pipe ~print =
    pipe_with ~decode:(fun state m -> decode_model ~state m) ~print
end
