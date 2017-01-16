
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Guards}

    This transformation removes "assuming" and "asserting" constructs and
    replaces them by boolean guards and assertions *)

open Nunchaku_core

module TI = TermInner
module Pol = Polarity
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module PPb = Problem.Print(P)(P)

let name = "intro_guards"
let section = Utils.Section.make name

type term = T.t

type state = {
  mutable lost_precision: bool;
  env: (T.t, T.t) Env.t;
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
    | l -> [f (U.and_nodup l)]
  and assuming = match g.assuming with
    | [] -> []
    | l -> [f (U.and_nodup l)]
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
  then U.imply (U.and_nodup g.assuming) (U.and_nodup (t :: g.asserting))
  else U.imply (U.and_nodup g.asserting) (U.and_nodup (t :: g.assuming))

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
  let ty = U.ty_exn ~sigma:(Env.find_ty ~env:state.env) t in
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
      | TI.Builtin ((`DataTest _ | `DataSelect _) as b), [t] ->
          let t', conds = tr_term ~state ~pol t in
          U.app_builtin b [t'], conds
      | _ ->
          (* combine side conditions from every sub-term *)
          let f, g_f = tr_term ~state ~pol f in
          (* under a function: no polarity *)
          let l, g = tr_list ~state ~pol:Pol.NoPol ~acc:g_f l in
          let t' = U.app f l in
          if is_prop ~state t then combine pol t' g else t', g
      end
  | TI.Builtin (`Not t) ->
      let t, g = tr_term ~state ~pol:(Pol.inv pol) t in
      combine pol (U.not_ t) g
  | TI.Builtin (`Or l) ->
      let l, g = tr_list ~state ~pol ~acc:empty_guard l in
      combine pol (U.or_ l) g
  | TI.Builtin (`And l) ->
      let l, g = tr_list ~state ~pol ~acc:empty_guard l in
      combine pol (U.and_ l) g
  | TI.Builtin (`Imply (a,b)) ->
      let a, g_a = tr_term ~state ~pol:(Pol.inv pol) a in
      let b, g_b = tr_term ~state ~pol b in
      combine pol (U.imply a b) (combine_guard g_a g_b)
  | TI.Builtin
    (`True | `False | `DataSelect _ | `DataTest _) ->
     (* partially applied, or constant *)
      t, empty_guard
  | TI.Builtin ((`Unparsable _ | `Undefined_self _ | `Undefined_atom _) as b) ->
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
            let pred, g = tr_term ~state ~pol:Pol.Neg pred in
            add_assuming acc (combine_polarized ~is_pos:true pred g))
          conds g.assuming
      in
      if is_prop ~state t
      then combine pol t conds
      else t, conds
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
          U.ite a (U.and_nodup g_b.asserting) (U.and_nodup g_c.asserting)
          :: g_a.asserting
        and assuming =
          U.ite a (U.and_nodup g_b.assuming) (U.and_nodup g_c.assuming)
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
          (* quantify over guards, too. We always quantify universally
              because the universal guard is valid in both polarities,
              whereas the existential guard would not. *)
          let g' = wrap_guard (U.forall v) g in
          U.mk_bind b v t, g'
      end
  | TI.Bind (`Fun, v, body) ->
      let body, g = tr_term ~state ~pol:Pol.NoPol body in
      begin match g.asserting, g.assuming with
        | [], [] -> U.fun_ v body, empty_guard
        | _ ->
          fail_tr_ t
            "@[translation of `%a` impossible:@ cannot put guards `%a` under λ@]"
            P.print t (TI.Builtin.pp_guard P.print) g
      end
  | TI.Bind (`Mu, _, _) -> fail_tr_ t "translation of µ impossible"
  | TI.Let (v,t,u) ->
      let t, g_t = tr_term t ~state ~pol:Pol.NoPol in
      let u, g_u = tr_term u ~state ~pol in
      let g = combine_guard (wrap_guard (U.let_ v t) g_u) g_t in
      if is_prop ~state u
      then combine pol (U.let_ v t u) g
      else U.let_ v t u, g
  | TI.Match (lhs, cases, def) ->
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
        and def =
          TI.map_default_case
            (fun rhs ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               combine_polarized ~is_pos rhs g_rhs)
            def
        in
        combine pol (U.match_with lhs cases ~def) g_lhs
      ) else (
        (* wrap guards in a pattern matching *)
        let asserting = ref ID.Map.empty in
        let asserting_def = ref ([],ID.Map.empty) in
        let assuming = ref ID.Map.empty in
        let assuming_def = ref ([],ID.Map.empty) in
        let cases = ID.Map.mapi
          (fun c (vars,rhs) ->
            let rhs, g_rhs = tr_term ~state ~pol rhs in
            asserting := ID.Map.add c (vars, g_rhs.asserting) !asserting;
            assuming := ID.Map.add c (vars, g_rhs.assuming) !assuming;
            vars,rhs)
          cases
        and def = TI.map_default_case'
            (fun rhs ids ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               asserting_def := g_rhs.asserting, ids;
               assuming_def := g_rhs.assuming, ids;
               rhs, ids)
            def
        in
        (* convert the map from constructors to guards, into one single
           guard that uses pattern matching *)
        let map_to_guard m def =
          if ID.Map.exists (fun _ (_,l) -> l<>[]) m || fst def <> []
          then
            let m = ID.Map.map (fun (vars,l) -> vars, U.and_ l) m in
            let def = match def with
              | [], _ -> TI.Default_none
              | l, ids ->
                assert (not (ID.Map.is_empty ids));
                TI.Default_some (U.and_ l, ids)
            in
            [U.match_with lhs m ~def]
          else []
        in
        let g_cases = {
          asserting = map_to_guard !asserting !asserting_def;
          assuming = map_to_guard !assuming !assuming_def;
        } in
        U.match_with lhs cases ~def, combine_guard g_cases g_lhs
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
  Utils.debugf ~section 5 "@[<2>intro guards in@ `@[%a@]`@]" (fun k->k P.print t);
  let pol = Pol.Pos in
  let t', g = tr_term ~state ~pol t in
  combine_polarized ~is_pos:true t' g

let encode_pb pb =
  let env = Problem.env pb in
  let state = { lost_precision=false; env; } in
  (* all polarities are positive at root, because we don't have [rec/pred]
     anymore thanks to {!inv} *)
  let pb' = Problem.map pb
    ~term:(tr_root ~state)
    ~ty:CCFun.id
  in
  (* if [state.lost_precision] then "UNSAT" means "UNKNOWN"
    TODO emit warning? *)
  if state.lost_precision
    then Utils.debug ~section 1 "lost precision, now UNSAT means UNKNOWN";
  Problem.add_unsat_means_unknown state.lost_precision pb'

let pipe ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after introduction of guards@}: %a@]@." PPb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  Transform.make
    ~on_encoded
    ~name
    ~encode:(fun p -> encode_pb p, ())
    ~decode:(fun () x -> x)
    ()
