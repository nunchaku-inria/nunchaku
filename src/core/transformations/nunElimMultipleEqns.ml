
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

module ID = NunID
module TI = NunTermInner
module Var = NunVar
module Stmt = NunStatement
module Subst = Var.Subst
module Env = NunEnv

type id = NunID.t
type 'a var = 'a Var.t

type ('a,'b) inv1 = <ty:'a; eqn:'b>
type 'a inv2 = <ty:'a; eqn:[`Single]>

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t
  type subst = (term,term) Subst.t

  exception Error of string

  let spf = CCFormat.sprintf

  let () = Printexc.register_printer
    (function
      | Error msg ->
          Some ("elimination of multiple equations: " ^ msg)
      | _ -> None)

  let error_ msg = raise (Error msg)
  let errorf_ msg = NunUtils.exn_ksprintf msg ~f:error_

  (* new [`Undefined] instance of [t] *)
  let mk_undefined t =
    let id = ID.make ~name:"u" in
    U.app_builtin (`Undefined id) [t]

  let mk_ite a b c = U.app_builtin `Ite [a;b;c]
  let mk_and l = U.app_builtin `And l

  type local_state = {
    root: term; (* term being pattern matched on (for undefined) *)
    env: term Env.t;
    subst: subst; (* for renaming variables, mostly *)
  }

  type pattern =
    | P_var of term var
    | P_term of term  (* should be a pattern, we will see *)
    | P_any (* no pattern, always succeeds *)

  (* returns a pair [l1, l2] where [l1] contains RHS terms with no side
     conditions, and [l2] contains RHS terms with their condition *)
  let extract_sides l =
    let rec aux noside_acc side_acc l = match l with
      | [] -> noside_acc, side_acc
      | (rhs, []) :: l' -> aux (rhs :: noside_acc) side_acc l'
      | (rhs, ((_::_) as sides) :: l' ->
          aux noside_acc ((mk_and sides, Yield rhs) :: side_acc) l'
    in
    aux [] [] l

  (* TODO: change a [equations] into a match tree *)
  (* transform flat equations into a match tree. *)
  let rec equations_to_match_tree ~local_state vars l =
    match vars, l with
    | _, [] -> mk_undefined local_state.root (* undefined case *)
    | [], [([], rhs, [])] ->
        (* simple case: no side conditions, one RHS *)
        U.eval ~subst:local_state.subst rhs
    | [], l ->
        (* add side conditions *)
        let noside, side = extract_sides l in
        begin match noside with
          | t1::t2::_, _ ->
              errorf_ "@[ambiguity: terms `@[%a@]`@ and `@[%a@]`@ have no side conditions@]"
                P.print t1 P.print t2
          | [], l ->
              (* try conditions one by one, fail otherwise *)
              let default = mk_undefined local_state.root in
              List.fold_left
                (fun acc (cond,rhs) ->
                  let rhs = U.eval ~subst:local_state.subst rhs in
                  mk_ite cond rhs acc)
                default l
          | [rhs], [] ->
              U.eval ~subst:local_state.subst rhs
          | [t], _::_ ->
              errorf_
                "@[ambiguity: term `@[%a@]`@ has no side conditions,@ but other terms do@]"
                P.print t
        end
    | v::vars', l ->
        (* match [v] against the first pattern of each element of [l] *)
        let trees = List.map
          (fun (pat::pats, rhs, side) ->
            pat, equations_to_match_tree ~local_state vars' [pats,rhs,side])
          l
        in
        Case (v, trees)

  let uniq_eqns
  : type a b.
    env:(term, term, (a,b) inv1) env ->
    id:id ->
    (term, term, (a,b) inv1) NunStatement.equations ->
    (term, term, a inv2) NunStatement.equations
  = fun ~env ~id e -> match e with
  | Stmt.Eqn_single (vars,rhs) -> Stmt.Eqn_single (vars, rhs)
  | Stmt.Eqn_linear l ->
      assert false  (* TODO: already done? should do a Ite on side conditions? *)
  | Stmt.Eqn_nested l ->
      (* create fresh vars *)
      let vars = match l with
        | [] -> assert false
        | (_, args, rhs, _) :: _ ->
            List.mapi
              (fun i a ->
                let ty = U.ty_exn ~sigma:(Env.find_ty ~env) a in
                Var.make ~ty (spf "v_%d" i))
              args
      and cases = List.map (fun (_,args,rhs,side) -> args, rhs, side) l in
      let local_state = {
        root=U.app (U.const id) (List.map U.var vars); (* defined term *)
        env;
        subst=Subst.empty;
      }
      equations_to_match_tree ~local_state vars cases

  let uniq_eqn_st env st =
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
        let l' = List.map
          (fun def ->
            let id = def.Stmt.rec_defined.Stmt.defined_head in
            let rec_eqns = uniq_eqns ~id ~env def.Stmt.rec_eqns in
            {def with Stmt.rec_eqns; }
          l
        in
        Stmt.axiom_rec ~info l'
    | Stmt.Axiom (Stmt.Axiom_spec l) -> env, Stmt.axiom_spec ~info l
    | Stmt.Axiom (Stmt.Axiom_std l) -> env, Stmt.axiom ~info l
    | Stmt.Decl (id,kind,ty) ->
        let env = Env.declare ~env id ty in
        env, Stmt.mk_decl ~info id kind ty
    | Stmt.TyDef (k,ty) ->
        (* declare (co)data, so it can be used in encoding *)
        let env = Env.def_data ~env ~kind:k ty in
        env, Stmt.mk_ty_def ~info k ty
    | Stmt.Goal g -> Stmt.goal ~info g

  let uniq_eqns_pb pb =
    let _, pb' = NunProblem.fold_map_statements pb
      ~f:uniq_eqn_st ~x:(Env.create()) in
    pb'

  let pipe ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = NunProblem.Print(P)(P) in
        [Format.printf "@[<v2>after uniq equations: %a@]@." PPb.print]
      else []
    and decode _ x = decode x in
    NunTransform.make1
      ~on_encoded
      ~name:"recursion_elim"
      ~encode:(fun p ->
        let p = uniq_eqns_pb p in
        p, ()
      ) ~decode
      ()
end


