
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Guards}

    This transformation removes "assuming" and "asserting" constructs and
    replaces them by boolean guards and assertions *)

module TI = TermInner
module Pol = Polarity
module Stmt = Statement

type inv = <ty:[`Mono]; eqn:[`Absent]; ind_preds:[`Absent]>

module Make(T : TI.S) : sig
  type term = T.t

  val encode_pb : (term, term, inv) Problem.t -> (term, term, inv) Problem.t

  (** Pipeline component *)
  val pipe :
    print:bool ->
    ((term, term, inv) Problem.t,
      (term, term, inv) Problem.t,
      'ret, 'ret) Transform.t
end = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PPb = Problem.Print(P)(P)

  type term = T.t

  type state = {
    sigma: term Signature.t;
  }

  type +'a guard = 'a TI.Builtin.guard = {
    assuming: 'a list;
    asserting: 'a list;
  }

  let empty_guard = {asserting=[]; assuming=[]}

  let combine_guard g1 g2 =
    { assuming=List.rev_append g1.assuming g2.assuming;
      asserting=List.rev_append g1.asserting g2.asserting;
    }

  let wrap_guard f g =
    let asserting = match g.asserting with
      | [] -> []
      | l -> [f (U.and_ l)]
    and assuming = match g.assuming with
      | [] -> []
      | l -> [f (U.and_ l)]
    in
    {assuming; asserting; }

  exception TranslationFailed of term * string
  (* not supposed to escape *)

  let fail_tr_ t msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

  let () = Printexc.register_printer
    (function
      | TranslationFailed (t,msg) ->
          Some (CCFormat.sprintf
            "@[<2>introduction of guards in@ `@[%a@]`@ failed:@ %s@]"
            P.print t msg)
      | _ -> None)

  let combine_polarized ~is_pos t g =
    if is_pos
    then U.imply (U.and_ g.assuming) (U.and_ (t :: g.asserting))
    else U.imply (U.and_ g.asserting) (U.and_ (t :: g.assuming))

  let add_asserting g p = { g with asserting = p::g.asserting }
  let add_assuming g p = { g with assuming = p::g.assuming }

  (* combine side-conditions with [t], depending on polarity *)
  let combine pol t g =
    if g.assuming=[] && g.asserting=[] then t, empty_guard
    else match pol with
    | Pol.Pos ->
        combine_polarized ~is_pos:true t g, empty_guard
    | Pol.Neg ->
        combine_polarized ~is_pos:false t g, empty_guard
    | Pol.NoPol -> t, g

  (* is [t] of type prop? *)
  let is_prop ~state t =
    let ty = U.ty_exn ~sigma:(Signature.find ~sigma:state.sigma) t in
    U.ty_is_Prop ty

  (* Translate term/formula recursively by removing asserting/assuming
     constructs.
     @returns new term, list of assertions, list of assumptions *)
  let rec tr_term ~state ~pol (t:term) : term * term guard =
    match T.repr t with
    | TI.Const _
    | TI.Var _ -> t, empty_guard
    | TI.App (f,l) ->
        begin match T.repr f, l with
        | TI.Builtin `Not, [t] ->
            let t, g = tr_term ~state ~pol:(Pol.inv pol) t in
            combine pol (U.not_ t) g
        | TI.Builtin ((`Or | `And) as b), l ->
            let l, g = tr_list ~state ~pol ~acc:empty_guard l in
            combine pol (U.app_builtin b l) g
        | TI.Builtin `Imply, [a;b] ->
            let a, g_a = tr_term ~state ~pol:(Pol.inv pol) a in
            let b, g_b = tr_term ~state ~pol b in
            combine pol (U.imply a b) (combine_guard g_a g_b)
        | TI.Builtin ((`DataTest _ | `DataSelect _) as b), [t] ->
            let t', conds = tr_term ~state ~pol t in
            U.app_builtin b [t'], conds
        | _ ->
            (* combine side conditions from every sub-term *)
            let f, g_f = tr_term ~state ~pol f in
            let l, g = tr_list ~state ~pol ~acc:g_f l in
            let t' = U.app f l in
            if is_prop ~state t then combine pol t' g else t', g
        end
    | TI.Builtin
      (`True | `False | `And | `Or | `Not
        | `Imply | `DataSelect _ | `DataTest _) ->
       (* partially applied, or constant *)
        t, empty_guard
    | TI.Builtin (`Undefined _ as b) ->
        let t' =
          U.builtin (TI.Builtin.map b ~f:(fun t-> fst(tr_term ~state ~pol t)))
        in
        t', empty_guard
    | TI.Builtin (`Guard (t, g)) ->
        let t, cond_t = tr_term ~state ~pol t in
        let conds =
          List.fold_left
            (fun acc pred ->
              let pred, g = tr_term ~state ~pol:Pol.Pos pred in
              (* apply guards to [pred] itself, then add [pred] to asserting *)
              add_asserting acc (combine_polarized ~is_pos:true pred g))
            cond_t g.asserting
        in
        let conds =
          List.fold_left
            (fun acc pred ->
              (* apply guards to [pred] itself, then add [pred] to assuming *)
              let pred, g = tr_term ~state ~pol:Pol.Pos pred in
              add_assuming acc (combine_polarized ~is_pos:true pred g))
            conds g.assuming
        in
        if is_prop ~state t
        then combine pol t conds
        else t, conds
    | TI.Builtin (`Equiv (a,b)) ->
        let a, g_a = tr_term ~state ~pol:Pol.NoPol a in
        let b, g_b = tr_term ~state ~pol:Pol.NoPol b in
        combine pol (U.equiv a b) (combine_guard g_a g_b)
    | TI.Builtin (`Eq (a,b)) ->
        let a, g_a = tr_term ~state ~pol:Pol.NoPol a in
        let b, g_b = tr_term ~state ~pol:Pol.NoPol b in
        combine pol (U.eq a b) (combine_guard g_a g_b)
    | TI.Builtin (`Ite (a,b,c)) ->
        let a, g_a = tr_term ~state ~pol:Pol.NoPol a in
        let b, g_b = tr_term ~state ~pol b in
        let c, g_c = tr_term ~state ~pol c in
        if is_prop ~state b && pol <> Pol.NoPol
        then (
          (* push guards in each branch of this boolean `if` *)
          let is_pos = match pol with
            | Pol.NoPol -> assert false
            | Pol.Pos -> true
            | Pol.Neg -> false
          in
          let b = combine_polarized ~is_pos b g_b in
          let c = combine_polarized ~is_pos c g_c in
          combine_polarized ~is_pos (U.ite a b c) g_a, empty_guard
        ) else (
          let asserting =
            U.ite a (U.and_ g_b.asserting) (U.and_ g_c.asserting)
            :: g_a.asserting
          and assuming =
            U.ite a (U.and_ g_b.assuming) (U.and_ g_c.assuming)
            :: g_a.assuming
          in
          U.ite a b c, {assuming; asserting;}
        )
    | TI.Bind ((`Forall | `Exists) as b, v, t) ->
        let t, g = tr_term ~state ~pol t in
        begin match pol with
        | Pol.Pos ->
            U.mk_bind b v (combine_polarized ~is_pos:true t g), empty_guard
        | Pol.Neg ->
            U.mk_bind b v (combine_polarized ~is_pos:false t g), empty_guard
        | Pol.NoPol ->
            (* quantify over guards, too *)
            let g' = wrap_guard (U.mk_bind b v) g in
            U.mk_bind b v t, g'
        end
    | TI.Bind (`Fun, _, _) -> fail_tr_ t "translation of λ impossible"
    | TI.Bind (`Mu, _, _) -> fail_tr_ t "translation of µ impossible"
    | TI.Let (v,t,u) ->
        let t, g_t = tr_term t ~state ~pol:Pol.NoPol in
        let u, g_u = tr_term u ~state ~pol in
        let g = combine_guard (wrap_guard (U.let_ v t) g_u) g_t in
        if is_prop ~state u
        then combine pol (U.let_ v t u) g
        else U.let_ v t u, g
    | TI.Match (lhs, cases) ->
        let lhs, g_lhs = tr_term ~state ~pol lhs in
        if is_prop ~state t && pol <> Pol.NoPol
        then (
          (* put guards in each branch *)
          let is_pos = match pol with
            | Pol.Pos -> true
            | Pol.Neg -> false
            | Pol.NoPol -> assert false
          in
          let cases = ID.Map.map
            (fun (vars,rhs) ->
              let rhs, g_rhs = tr_term ~state ~pol rhs in
              vars, combine_polarized ~is_pos rhs g_rhs)
            cases
          in
          combine pol (U.match_with lhs cases) g_lhs
        ) else (
          (* wrap guards in a pattern matching *)
          let asserting = ref ID.Map.empty in
          let assuming = ref ID.Map.empty in
          let cases = ID.Map.mapi
            (fun c (vars,rhs) ->
              let rhs, g_rhs = tr_term ~state ~pol rhs in
              asserting := ID.Map.add c (vars, g_rhs.asserting) !asserting;
              assuming := ID.Map.add c (vars, g_rhs.assuming) !assuming;
              vars,rhs)
            cases
          in
          (* convert the map from constructors to guards, into one single
             guard that uses pattern matching *)
          let map_to_guard m =
            if ID.Map.exists (fun _ (_,l) -> l<>[]) m
            then
              let m = ID.Map.map (fun (vars,l) -> vars, U.and_ l) m in
              [U.match_with lhs m]
            else []
          in
          let g_cases = {
            asserting = map_to_guard !asserting;
            assuming = map_to_guard !assuming;
          } in
          U.match_with lhs cases, combine_guard g_cases g_lhs
        )
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, empty_guard
    | TI.Bind (`TyForall, _, _)
    | TI.TyMeta _ -> assert false

  (* translate each element of [l], combining the guards into [acc] *)
  and tr_list ~state ~pol ~acc l =
    let acc, l =
      Utils.fold_map
        (fun acc t ->
          let t', g = tr_term ~state ~pol t in
          combine_guard g acc, t')
        acc l
    in
    l, acc

  let tr_root ~state t =
    let pol = Pol.Pos in
    let t', g = tr_term ~state ~pol t in
    combine_polarized ~is_pos:true t' g

  let encode_pb pb =
    let sigma = Problem.signature pb in
    let state = { sigma; } in
    (* all polarities are positive at root, because we don't have [rec/pred]
       anymore thanks to {!inv} *)
    Problem.map pb
      ~term:(tr_root ~state)
      ~ty:CCFun.id

  let pipe ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after introduction of guards: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name:"intro_guards"
      ~encode:(fun p -> encode_pb p, ())
      ~decode:(fun () x -> x)
      ()
end
