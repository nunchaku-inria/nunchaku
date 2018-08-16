
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Guards}

    This transformation removes "assuming" and "asserting" constructs and
    replaces them by boolean guards and assertions *)

open Nunchaku_core

module TI = TermInner
module Pol = Polarity
module Stmt = Statement
module T = Term
module PPb = Problem.P

let name = "intro_guards"
let section = Utils.Section.make name

type term = T.t

type state = {
  mutable lost_precision: bool;
  env: (T.t, T.t) Env.t;
}

type +'a guard = 'a Builtin.guard = {
  asserting: 'a list;
}

let empty_guard = Builtin.empty_guard

let combine_guard = Builtin.merge_guard

let wrap_guard f g =
  let asserting = match g.asserting with
    | [] -> []
    | l -> [f (T.and_nodup l)]
  in
  { asserting; }

exception TranslationFailed of term * string
(* not supposed to escape *)

let fail_tr_ t msg =
  Utils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

let () = Printexc.register_printer
    (function
      | TranslationFailed (t,msg) ->
        Some (CCFormat.sprintf
            "@[<2>introduction of guards in@ `@[%a@]`@ failed:@ %s@]"
            T.pp t msg)
      | _ -> None)

let combine_polarized ~is_pos t g =
  if is_pos
  then T.and_nodup (t :: g.asserting)
  else T.imply (T.and_nodup g.asserting) t

let add_asserting g p = { asserting = p::g.asserting }

(* combine side-conditions with [t], depending on polarity *)
let combine pol t g =
  if g.asserting=[] then t, empty_guard
  else match pol with
    | Pol.Pos ->
      combine_polarized ~is_pos:true t g, empty_guard
    | Pol.Neg ->
      combine_polarized ~is_pos:false t g, empty_guard
    | Pol.NoPol -> t, g

(* is [t] of type prop? *)
let is_prop ~state t =
  let ty = T.ty_exn ~env:state.env t in
  T.ty_is_Prop ty

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
          T.app_builtin b [t'], conds
        | _ ->
          (* combine side conditions from every sub-term *)
          let f, g_f = tr_term ~state ~pol f in
          (* under a function: no polarity *)
          let l, g = tr_list ~state ~pol:Pol.NoPol ~acc:g_f l in
          let t' = T.app f l in
          if is_prop ~state t then combine pol t' g else t', g
      end
    | TI.Builtin (`Not t) ->
      let t, g = tr_term ~state ~pol:(Pol.inv pol) t in
      combine pol (T.not_ t) g
    | TI.Builtin (`Or l) ->
      let l, g = tr_list ~state ~pol ~acc:empty_guard l in
      combine pol (T.or_ l) g
    | TI.Builtin (`And l) ->
      let l, g = tr_list ~state ~pol ~acc:empty_guard l in
      combine pol (T.and_ l) g
    | TI.Builtin (`Imply (a,b)) ->
      let a, g_a = tr_term ~state ~pol:(Pol.inv pol) a in
      let b, g_b = tr_term ~state ~pol b in
      combine pol (T.imply a b) (combine_guard g_a g_b)
    | TI.Builtin
        (`True | `False | `DataSelect _ | `DataTest _) ->
      (* partially applied, or constant *)
      t, empty_guard
    | TI.Builtin ((`Unparsable _ | `Undefined_self _
                  | `Undefined_atom _ | `Card_at_least _) as b) ->
      let t' =
        T.builtin (Builtin.map b ~f:(fun t-> fst(tr_term ~state ~pol t)))
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
      if is_prop ~state t
      then combine pol t conds
      else t, conds
    | TI.Builtin (`Eq (a,b)) ->
      let a, g_a = tr_term ~state ~pol:Pol.NoPol a in
      let b, g_b = tr_term ~state ~pol:Pol.NoPol b in
      combine pol (T.eq a b) (combine_guard g_a g_b)
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
        combine_polarized ~is_pos (T.ite a b c) g_a, empty_guard
      ) else (
        let asserting =
          T.ite a (T.and_nodup g_b.asserting) (T.and_nodup g_c.asserting)
          :: g_a.asserting
        in
        T.ite a b c, {asserting}
      )
    | TI.Bind ((Binder.Forall | Binder.Exists) as b, v, t) ->
      let t, g = tr_term ~state ~pol t in
      begin match pol with
        | Pol.Pos ->
          T.mk_bind b v (combine_polarized ~is_pos:true t g), empty_guard
        | Pol.Neg ->
          T.mk_bind b v (combine_polarized ~is_pos:false t g), empty_guard
        | Pol.NoPol ->
          (* quantify over guards, too. We always quantify universally
              because the universal guard is valid in both polarities,
              whereas the existential guard would not. *)
          let g' = wrap_guard (T.forall v) g in
          T.mk_bind b v t, g'
      end
    | TI.Bind (Binder.Fun, v, body) ->
      let body, g = tr_term ~state ~pol:Pol.NoPol body in
      begin match g.asserting with
        | [] -> T.fun_ v body, empty_guard
        | _ ->
          fail_tr_ t
            "@[translation of `%a` impossible:@ cannot put guards `%a` under λ@]"
            T.pp t (Builtin.pp_guard T.pp) g
      end
    | TI.Bind (Binder.Mu, _, _) -> fail_tr_ t "translation of µ impossible"
    | TI.Let (v,t,u) ->
      let t, g_t = tr_term t ~state ~pol:Pol.NoPol in
      let u, g_u = tr_term u ~state ~pol in
      let g = combine_guard (wrap_guard (T.let_ v t) g_u) g_t in
      if is_prop ~state u
      then combine pol (T.let_ v t u) g
      else T.let_ v t u, g
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
            (fun (tys,vars,rhs) ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               tys, vars, combine_polarized ~is_pos rhs g_rhs)
            cases
        and def =
          TI.map_default_case
            (fun rhs ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               combine_polarized ~is_pos rhs g_rhs)
            def
        in
        combine pol (T.match_with lhs cases ~def) g_lhs
      ) else (
        (* wrap guards in a pattern matching *)
        let asserting = ref ID.Map.empty in
        let asserting_def = ref ([],ID.Map.empty) in
        let cases = ID.Map.mapi
            (fun c (tys,vars,rhs) ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               asserting := ID.Map.add c (tys, vars, g_rhs.asserting) !asserting;
               tys,vars,rhs)
            cases
        and def = TI.map_default_case'
            (fun rhs ids ->
               let rhs, g_rhs = tr_term ~state ~pol rhs in
               asserting_def := g_rhs.asserting, ids;
               rhs, ids)
            def
        in
        (* convert the map from constructors to guards, into one single
           guard that uses pattern matching *)
        let map_to_guard m def =
          if ID.Map.exists (fun _ (_,_,l) -> l<>[]) m || fst def <> []
          then (
            let m = ID.Map.map (fun (tys,vars,l) -> tys, vars, T.and_ l) m in
            let def = match def with
              | [], _ -> None
              | l, ids ->
                assert (not (ID.Map.is_empty ids));
                Some (T.and_ l, ids)
            in
            [T.match_with lhs m ~def]
          ) else []
        in
        let g_cases = {
          asserting = map_to_guard !asserting !asserting_def;
        } in
        T.match_with lhs cases ~def, combine_guard g_cases g_lhs
      )
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t, empty_guard
    | TI.Bind (Binder.TyForall, _, _)
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
  Utils.debugf ~section 5 "@[<2>intro guards in@ `@[%a@]`@]" (fun k->k T.pp t);
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
      let module PPb = Problem.P in
      Format.printf "@[<v2>@{<Yellow>after introduction of guards@}: %a@]@." PPb.pp)
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
