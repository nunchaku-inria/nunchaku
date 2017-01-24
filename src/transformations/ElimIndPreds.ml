
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Inductive Predicates} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)

let name = "elim_ind_pred"

let section = Utils.Section.make name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "@[<2>elim_ind_pred:@ %s@]" msg)
      | _ -> None)

type term = T.t
type subst = (term,term) Var.Subst.t
type decode_state = unit

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

(** How to eliminate inductive predicates *)
type mode =
  [ `Use_selectors
  (** guard sub-cases with data_select and data_test *)

  | `Use_match
    (** use pattern-matching for picking sub-cases *)
  ]

exception ExitAsCstors

(* if [t = c1(c2_1(...), c2_2(...), ...)] recursively, where each [c_] is
   a (co)data constructor and leaves are variables, then this returns
   [Some (conds, subst')] where:
     - [conds] is a set of conditions for [t] to have the given shape.
       Each condition uses [Term.data_test] and [Term.data_select] to express
       some property on the shape of some subterms of [root].
     - [subst'] is an extension of [subst] that binds leaf variables
       to selector-expressions on [root]
   @param env environment
   @param root the term that must have the shaped described by [t]
*)
let as_cstor_guards ~env ~subst ~root t : (subst * term list) option =
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
    | TI.Const id when Env.is_cstor (Env.find_exn ~env id) ->
      (* nullary constructor, easy *)
      conds := U.eq select t :: !conds;
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

(* add conditions [conds] and substitution [subst]
   such that [conds => subst(vars) = subst(args)].
   For optimization purpose, we replace
     `∃ y, x=s (s y) && p[y]`
     with
     `is-succ x && is-succ (pred x) && p[pred (pred x)]` *)
let encode_clause_selectors ~env vars args ~c_vars ~c_guard =
  let subst, conds =
    List.fold_left2
      (fun (subst,conds) v arg ->
         match T.repr arg with
           | TI.Var v' ->
             (* [arg_i = v'], so making [arg_i = v] is as simple as [v' := v] *)
             Var.Subst.add ~subst v' (U.var v), conds
           | _ ->
             (* extend [subst, conds] so that [conds => subst(v)=arg] *)
             begin match as_cstor_guards ~env ~subst arg ~root:(U.var v) with
               | Some (subst', conds') ->
                 subst', conds' @ conds
               | None ->
                 (* default: just add constraint [arg_i = v] *)
                 subst, U.eq (U.var v) arg :: conds
             end)
      (Var.Subst.empty, [])
      vars args
  in
  let conds = List.rev_map (U.eval ~rec_:false ~subst) conds in
  (* add guard, if any *)
  let all_conds = match c_guard with
    | None -> U.and_ conds
    | Some g -> U.and_ (U.eval ~subst g :: conds)
  in
  (* quantify over the clause's variables that are not eliminated *)
  let cvars =
    List.filter
      (fun v -> not (Var.Subst.mem ~subst v))
      c_vars in
  U.exists_l cvars all_conds

(* build a [TermInner.default_case] that returns [t] and
   covers every constructor of [typeof c_id] but [c_id] *)
let match_default_except ~env c_id t : _ TI.default_case =
  let info = Env.find_exn ~env c_id in
  begin match Env.def info with
    | Env.Cstor (_, _, ty_def, _) ->
      let map =
        ID.Map.values ty_def.Stmt.ty_cstors
        |> Sequence.filter
          (fun cstor -> not (ID.equal cstor.Stmt.cstor_name c_id))
        |> Sequence.map
          (fun cstor ->
             let arity = U.ty_num_param cstor.Stmt.cstor_type in
             cstor.Stmt.cstor_name, arity)
        |> ID.Map.of_seq
      in
      TI.Default_some (t, map)
    | _ -> errorf_ "`%a` should be a constructor" ID.print c_id
  end

(* build a match tree [t] such that [vars=args => t --> k()]
   and any input incompatible with [args] will reduce [t] to [false].
   For instance, if [vars=x,y] and [args=S x1, Nil],
   then [t = match x with
          | S x2 ->
            match y with
              | Nil -> k subst
              | _ -> false
            end
          | _ -> false]
   @param k the leaf to put inside the only successful branch
     of the tree: [k subst conds] must return some boolean term,
    where [subst] is a substitution of a subset of [freevars(args)]
     and [conds] are side-conditions to satisfy
   @param vars the new input variables, we are defining [some_pred vars := …]
      from a clause [forall …. guard => some_pred args]
*)
let mk_match_tree ~env ~subst vars args ~k : term =
  assert (List.length vars = List.length args);
  (* [subst]: current substitution on vars(args)
     [conds]: set of side conditions (non-linear matching) *)
  let rec aux subst conds vars args = match vars, args with
    | [], [] ->
      (* Successful branch. *)
      k subst conds
    | [], _
    | _, [] -> assert false
    | v :: vars_tail, arg :: args_tail ->
      (* we need to express that [v = arg] *)
      (* default case: [if (v=arg) then (recurse) else false] *)
      let default() =
        let cond = U.eq (U.var v) arg in
        aux subst (cond::conds) vars_tail args_tail
      in
      (* try to use pattern matching, which is more accurate and efficient *)
      begin match T.repr arg with
        | TI.Var v_a ->
          begin match Var.Subst.find ~subst v_a with
            | None ->
              (* bind [v_a] to [v] *)
              let subst = Var.Subst.add ~subst v_a (U.var v) in
              aux subst conds vars_tail args_tail
            | Some t ->
              (* [v_a = v] and [v_a = t], so we better make sure that [v = t] *)
              let conds = U.eq (U.var v) t :: conds in
              aux subst conds vars_tail args_tail
          end
        | TI.Const c_id when Env.is_cstor (Env.find_exn ~env c_id) ->
          (* nullary constructor, just match [v] with it *)
          let ok_case =
            aux subst conds vars_tail args_tail
          and default =
            match_default_except ~env c_id U.false_
          in
          U.match_with (U.var v) (ID.Map.singleton c_id ([], ok_case)) ~def:default
        | TI.App (f, l) ->
          begin match T.repr f with
            | TI.Const c_id ->
              let info = Env.find_exn ~env c_id in
              let ty_id = Env.ty info in
              let _, ty_args, _ = U.ty_unfold ty_id in
              begin match Env.def info with
                | Env.Cstor _ ->
                  (* A constructor [c_id l]. We pattern-match [v]
                     and continue in the [c_id] case with fresh variables. *)
                  assert (List.length ty_args = List.length l);
                  let new_vars =
                    List.mapi
                      (fun i sub_ty -> Var.makef ~ty:sub_ty "x_%d" i)
                      ty_args
                  in
                  (* the successful branch *)
                  let ok_case =
                    aux subst conds (vars_tail @ new_vars) (args_tail @ l)
                  and default =
                    match_default_except ~env c_id U.false_
                  in
                  U.match_with (U.var v)
                    (ID.Map.singleton c_id (new_vars,ok_case))
                    ~def:default
                | _ -> default()
              end
            | _ -> default()
          end
        | _ ->
          default()
      end
  in
  aux subst [] vars args

(* build a term [t(vars)] such that [t(args/vars) => clause_conclusion(args)].
   The term [t] is a pattern-match tree with all branches but one reducing
   to false, and the last branch corresponds to [vars=args] and yields [guard]
   (or [true] if there is no guard) *)
let encode_clause_match ~env vars args ~c_vars ~c_guard =
  let res =
    mk_match_tree ~env ~subst:Var.Subst.empty vars args
      ~k:(fun subst conds ->
        (* gather elements of [c_vars] that are not bound in [subst], and
           quantify existentially on them *)
        let ex_vars =
          List.filter (fun v -> not (Var.Subst.mem ~subst v)) c_vars
        in
        (* all variables of [args] should be bound *)
        let all_conds =
          CCList.cons_maybe c_guard conds
          |> U.and_
        in
        begin match T.repr all_conds with
          | TI.Builtin `True -> U.true_
          | _ ->
            U.exists_l ex_vars (U.eval ~subst all_conds)
        end)
  in
  res

(* encode clause [c] into a propositional term [t] such that [t => id vars] *)
let encode_clause ~mode ~env (id:ID.t) vars (c:(_,_) Stmt.pred_clause): term =
  let arity = List.length vars in
  (* the clause should be [guard => id args], here we extract [args] from
     [c.conclusion] *)
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
  match mode with
    | `Use_selectors ->
      encode_clause_selectors ~env vars args
        ~c_vars:c.Stmt.clause_vars ~c_guard:c.Stmt.clause_guard
    | `Use_match ->
      encode_clause_match ~env vars args
        ~c_vars:c.Stmt.clause_vars ~c_guard:c.Stmt.clause_guard

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
  : mode:mode ->
  env:(term, term) Env.t ->
  (term, term) Stmt.pred_def ->
  (term, term) Stmt.rec_def
  = fun ~mode ~env pred ->
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
    (* translate clauses into one existentially quantified case,
       then take the disjunction *)
    let cases =
      List.map
        (fun c -> encode_clause ~mode ~env id vars c)
        pred.Stmt.pred_clauses
    in
    let rhs = U.or_ cases in
    {Stmt.
      rec_defined=d;
      rec_ty_vars=[];
      rec_eqns=Stmt.Eqn_single (vars,rhs);
    }

let elim_ind_preds
    ~(mode:mode)
    (pb: (term,term)Problem.t)
  : (term, term) Problem.t * decode_state =
  let env = Problem.env pb in
  let pb' = Problem.flat_map_statements pb
      ~f:(fun st ->
        let info = Stmt.info st in
        match Stmt.view st with
          | Stmt.Pred (`Wf, _, l) ->
            (* well-founded: translate directly to recursive functions *)
            let l = List.map (pred_to_def ~mode ~env) l in
            [Stmt.axiom_rec ~info l]
          | Stmt.Pred (`Not_wf, _, _) ->
            (* should have been  transformed into a [`Wf] (co)predicate
               by polarize *)
            Utils.not_implemented
              "cannot eliminate non-well-founded predicates without polarization"
          | Stmt.Decl d -> [Stmt.decl_of_defined ~info d]
          | Stmt.Copy c -> [Stmt.copy ~info c]
          | Stmt.Axiom (Stmt.Axiom_std l) -> [Stmt.axiom ~info l]
          | Stmt.Axiom (Stmt.Axiom_spec l) -> [Stmt.axiom_spec ~info l]
          | Stmt.Axiom (Stmt.Axiom_rec l) -> [Stmt.axiom_rec ~info l]
          | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l]
          | Stmt.Goal g -> [Stmt.goal ~info g]
      )
  in
  pb', ()

let decode_model ~state:_ m = m

let pipe_with ~decode ~print ~check ~mode =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after elimination of inductive predicates@}:@ %a@]@." Ppb.print)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  and new_features = match mode with
    | `Use_selectors -> []
    | `Use_match -> Transform.Features.([Match, Present])
  in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list
          [Ty, Mono; Ind_preds, Present; Eqn, Eqn_single])
    ~map_spec:Transform.Features.(
        update_l ((Ind_preds, Absent) :: new_features))
    ~on_encoded
    ~encode:(fun pb -> elim_ind_preds ~mode pb)
    ~decode
    ()

let pipe ~print ~check ~mode =
  pipe_with ~print ~check ~mode
    ~decode:(fun state -> Problem.Res.map_m ~f:(decode_model ~state))
