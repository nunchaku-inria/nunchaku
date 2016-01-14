
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst

type id = ID.t

type ('a,'b) inv1 = <ty:'a; ind_preds:'b; eqn:[`Nested]>
type ('a,'b) inv2 = <ty:'a; ind_preds:'b; eqn:[`Single]>

let section = Utils.Section.make "elim_multiple_eqns"

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module Pat = Pattern.Make(T)

  type term = T.t
  type ('a,'b) env = (term,term,<eqn:[`Single];ind_preds:'b;ty:'a>) Env.t

  exception Error of string

  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | Error msg ->
          Some (spf "@[<2>elimination of multiple equations:@ %s@]" msg)
      | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

  type ('a,'b) local_state = {
    root: term; (* term being pattern matched on (for undefined) *)
    env: ('a,'b) env;
  }

  type pattern =
    | P_term of term  (* should be a pattern, we will see *)
    | P_any (* no pattern, always succeeds *)

  and ('a, 'b) decision_node =
    | DN_match of ('a, 'b) decision_node_match
    | DN_if of 'b list * 'b list  (* true/false *)
    | DN_bind of 'b list (* only accepts variables *)

  and ('a, 'b) decision_node_match = {
    dn_tydef: term Stmt.tydef; (* all constructors required *)
    dn_by_cstor: 'a list ID.Map.t;
    dn_wildcard: 'b list; (* matching anything *)
  }

  let dnode_add_wildcard d x = match d with
    | DN_if (l,r) -> DN_if (x::l, x::r)
    | DN_match d -> DN_match { d with dn_wildcard=x :: d.dn_wildcard }
    | DN_bind d -> DN_bind (x::d)

  let dnode_add_bool d b x = match d, b with
    | DN_if (l,r), `True -> DN_if (x::l,r)
    | DN_if (l,r), `False -> DN_if (l,x::r)
    | DN_bind _, _
    | DN_match _, _ ->
        errorf_ "@[<2>expected boolean decision node@]"

  let dnode_add_cstor d c x = match d with
    | DN_match d ->
        let allowed_cstors = d.dn_tydef.Stmt.ty_cstors in
        if not (ID.Map.mem c allowed_cstors)
        then errorf_ "@[<2>%a is not a constructor of %a@ (these are @[%a@])@]"
          ID.print c ID.print d.dn_tydef.Stmt.ty_id
          (CCFormat.seq ID.print) (ID.Map.to_seq allowed_cstors |> Sequence.map fst);
        let l = try ID.Map.find c d.dn_by_cstor with Not_found -> [] in
        DN_match { d with dn_by_cstor = ID.Map.add c (x::l) d.dn_by_cstor }
    | DN_if _ -> errorf_ "cannot match against %a, boolean case" ID.print c
    | DN_bind _ ->
        errorf_ "cannot match against %a, variable binding only" ID.print c

  (* returns a pair [l1, l2] where [l1] contains RHS terms with no side
     conditions, and [l2] contains RHS terms with their condition *)
  let extract_side_conds l =
    let rec aux noside_acc side_acc l = match l with
      | [] -> noside_acc, side_acc
      | (rhs, [], subst) :: l' -> aux ((rhs,subst) :: noside_acc) side_acc l'
      | (rhs, ((_::_) as sides), subst) :: l' ->
          aux noside_acc ((U.and_ sides, rhs, subst) :: side_acc) l'
    in
    aux [] [] l

  (* transform flat equations into a match tree. *)
  let rec compile_equations ~local_state vars l : term =
    match vars, l with
    | _, [] -> U.undefined_ local_state.root (* undefined case *)
    | [], [([], rhs, [], subst)] ->
        (* simple case: no side conditions, one RHS *)
        U.eval ~subst rhs
    | [], l ->
        let l = List.map
          (fun (args,rhs,side,subst) ->
            assert (args=[]);
            rhs,side,subst)
          l
        in
        (* add side conditions *)
        let noside, side = extract_side_conds l in
        begin match noside, side with
          | (t1,_)::(t2,_)::_, _ ->
              errorf_ "@[ambiguity: terms `@[%a@]`@ and `@[%a@]`@ have no side conditions@]"
                P.print t1 P.print t2
          | [], l ->
              (* try conditions one by one, fail otherwise *)
              let default = U.undefined_ local_state.root in
              List.fold_left
                (fun acc (cond,rhs,subst) ->
                  let rhs = U.eval ~subst rhs in
                  U.ite cond rhs acc)
                default l
          | [rhs,subst], [] ->
              U.eval ~subst rhs
          | [t,_], _::_ ->
              errorf_
                "@[ambiguity: term `@[%a@]`@ has no side conditions,@ but other terms do.@]"
                P.print t
        end
    | v::vars', _ ->
        (* obtain the relevant type definition *)
        (* build one node of the decision tree *)
        let dnode =
          Utils.debugf ~section 5 "build decision node for %a:%a"
            (fun k->k Var.print v P.print (Var.ty v));
          let ty = Var.ty v in
          if U.ty_is_Prop ty then DN_if ([], [])
          else try
            let ty_id = U.head_sym ty in
            match Env.def (Env.find_exn ~env:local_state.env ty_id) with
            | Env.Data (_, _, tydef) ->
                DN_match {
                  dn_tydef=tydef;
                  dn_by_cstor=ID.Map.empty;
                  dn_wildcard=[];
                }
            | Env.Fun_def (_,_,_)
            | Env.Fun_spec _
            | Env.Pred _
            | Env.Copy_abstract _
            | Env.Copy_concretize _
            | Env.Cstor (_,_,_,_) ->
                errorf_ "@[%a is not a type.@]" ID.print ty_id
            | Env.Copy_ty _
            | Env.NoDef -> DN_bind []
          with Not_found ->
            DN_bind [] (* not an atomic type *)
        in
        let dnode = List.fold_left
          (fun dnode (pats, rhs, side, subst) ->
            let pat, pats = match pats with [] -> assert false | x::y -> x,y in
            match pat with
            | P_any -> dnode_add_wildcard dnode (pats,rhs,side,subst)
            | P_term t ->
                match Pat.repr t with
                | Pattern.Builtin ((`True | `False) as b) ->
                    (* follow the [true] branch *)
                    dnode_add_bool dnode b (pats,rhs,side,subst)
                | Pattern.App (id,sub_pats) ->
                    (* follow the [id] branch *)
                    let sub_pats = List.map (fun x->P_term x) sub_pats in
                    dnode_add_cstor dnode id (sub_pats,pats,rhs,side,subst)
                | Pattern.Var v' ->
                    (* renaming *)
                    let subst = Subst.add ~subst v' (U.var v) in
                    dnode_add_wildcard dnode (pats,rhs,side,subst)
          )
          dnode l
        in
        compile_dnode ~local_state v vars' dnode

  (* add missing constructors (not explicitely matched upon) to the set
     of cases, complemented with a list of fresh vars, leading to
     the default cases;
     then compile the subtrees *)
  and compile_dnode ~local_state v next_vars dn : term = match dn with
  | DN_if (l,r) ->
      let l = compile_equations ~local_state next_vars l in
      let r = compile_equations ~local_state next_vars r in
      U.ite (U.var v) l r
  | DN_bind l -> compile_equations ~local_state next_vars l
  | DN_match dn when ID.Map.is_empty dn.dn_by_cstor ->
      (* no need to match, use next variables *)
      compile_equations ~local_state next_vars dn.dn_wildcard
  | DN_match dn ->
      (* one level of matching *)
      let l = ID.Map.map
        (fun cstor ->
          let id = cstor.Stmt.cstor_name in
          Utils.debugf ~section 5 "compile_dnode for %a on cstor %a"
            (fun k -> k Var.print v ID.print id);
          (* fresh vars for the constructor's arguments *)
          let vars = List.mapi
            (fun i ty -> Var.make ~ty ~name:(spf "v_%d" i))
            cstor.Stmt.cstor_args
          in
          (* the cases that always match *)
          let wildcard_cases = List.map
            (fun (pats,rhs,side,subst) ->
              List.map (fun _ -> P_any) vars @ pats, rhs, side, subst)
            dn.dn_wildcard
          in
          (* does this constructor also have some explicit branches? *)
          let cases =
            try
              let l = ID.Map.find id dn.dn_by_cstor in
              assert (l <> []);
              List.map
                (fun (new_pats,pats,rhs,side,subst) ->
                  assert (List.length new_pats=List.length vars);
                  new_pats @ pats, rhs, side, subst)
                l
            with Not_found -> []
          in
          let rhs' =compile_equations ~local_state
            (vars @ next_vars) (cases @ wildcard_cases)
          in
          vars, rhs'
        )
        dn.dn_tydef.Stmt.ty_cstors
      in
      U.match_with (U.var v) l

  (* @param env the environment for types and constructors
     @param id the symbol being defined
  *)
  let uniq_eqns
  : type a b.
    env:(a,b) env ->
    id:id ->
    (term, term, (a,b) inv1) Statement.equations ->
    (term, term, (a,b) inv2) Statement.equations
  = fun ~env ~id (Stmt.Eqn_nested l) ->
      (* create fresh vars *)
      let vars = match l with
        | [] -> assert false
        | (_, args, _, _) :: _ ->
            List.mapi
              (fun i a ->
                let ty = U.ty_exn ~sigma:(Env.find_ty ~env) a in
                Var.make ~ty ~name:(spf "v_%d" i))
              args
      in
      let cases =
        List.map
          (fun (_,args,rhs,side) ->
            let pats = List.map (fun t -> P_term t) args in
            pats, rhs, side, Subst.empty)
          l
      and local_state = {
        root=U.app (U.const id) (List.map U.var vars); (* defined term *)
        env;
      } in
      let new_rhs = compile_equations ~local_state vars cases in
      Stmt.Eqn_single (vars,new_rhs)

  let conv_preds
  : type a b.
    ('t, 'ty, (a,b) inv1) Stmt.pred_def list ->
    ('t, 'ty, (a,b) inv2) Stmt.pred_def list
  = fun l -> (Obj.magic l)

  let uniq_eqn_st env st =
    let loc = Stmt.loc st in
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        let l' = List.map
          (fun def ->
            let id = def.Stmt.rec_defined.Stmt.defined_head in
            let rec_eqns = uniq_eqns ~id ~env def.Stmt.rec_eqns in
            {def with Stmt.rec_eqns; })
          l
        in
        let env = Env.declare_rec_funs ?loc ~env l' in
        env, Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) ->
        env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) ->
        env, Stmt.axiom ~info l
    | Stmt.Decl (id,kind,ty) ->
        let env = Env.declare ?loc ~env ~kind id ty in
        env, Stmt.mk_decl ~info id kind ty
    | Stmt.TyDef (k,ty) ->
        (* declare (co)data, so it can be used in encoding *)
        let env = Env.def_data ?loc ~env ~kind:k ty in
        env, Stmt.mk_ty_def ~info k ty
    | Stmt.Pred (wf, k, l) ->
        let l = conv_preds l in
        let env = Env.def_preds ?loc ~env ~wf ~kind:k l in
        env, Stmt.mk_pred ~info ~wf k l
    | Stmt.Copy c ->
        let env = Env.add_copy ?loc ~env c in
        env, Stmt.copy ~info c
    | Stmt.Goal g ->
        env, Stmt.goal ~info g

  let uniq_eqns_pb pb =
    let _, pb' = Problem.fold_map_statements pb
      ~f:uniq_eqn_st ~x:(Env.create()) in
    pb'

  let pipe ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after uniq equations: %a@]@." PPb.print]
      else []
    and decode _ x = decode x in
    Transform.make1
      ~on_encoded
      ~name:"elim_multi_eqns"
      ~encode:(fun p ->
        let p = uniq_eqns_pb p in
        p, ()
      ) ~decode
      ()
end


