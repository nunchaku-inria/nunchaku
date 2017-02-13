(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = TermInner
module Subst = Var.Subst

type 'a printer = Format.formatter -> 'a -> unit
type 'a prec_printer = Precedence.t -> 'a printer
type 'a to_sexp = 'a -> Sexp_lib.t

let fpf = Format.fprintf

(** {2 Decision Trees}

    A decision tree is a nested if/then/else used to describe functions
    over finite domains. *)

module DT = struct
  (* a decision tree *)
  type (+'t, +'ty) t =
    | Yield of 't
    | Cases of ('t, 'ty) cases

  (* a nested if/then/else on a given variable *)
  and (+'t, +'ty) cases = {
    var: 'ty Var.t;
    (* the variable being tested *)
    tests: ('t, 'ty) tests_or_match;
    (* list of [if var=term, then sub-dt] *)
    default: ('t, 'ty) t option;
    (* sub-dt by default *)
  }

  and ('t, 'ty) tests_or_match =
    | Tests of ('t, 'ty) case list
    | Match of
        ('ty Var.t list * ('t, 'ty) t) ID.Map.t (* branches *)
        * int ID.Map.t (* missing cases *)

  and ('t, 'ty) case = 't * ('t, 'ty) t

  let tests_ t = Tests t
  let match_ ~missing t = Match (t,missing)

  let yield t = Yield t

  let mk_tests v ~tests ~default =
    if tests=[] && default=None then invalid_arg "DT.cases";
    Cases { var=v; tests=Tests tests; default; }

  let mk_match v ~by_cstor ~missing ~default =
    if ID.Map.is_empty by_cstor && default=None then invalid_arg "DT.match";
    Cases { var=v; tests=Match (by_cstor,missing); default; }

  let mk_cases v x ~default = match x with
    | Tests l -> mk_tests v ~tests:l ~default
    | Match (m,missing) -> mk_match v ~by_cstor:m ~missing ~default

  let rec const vars ret = match vars with
    | [] -> ret
    | v :: vars' ->
      let default = Some (const vars' ret) in
      mk_tests v ~tests:[] ~default

  let map_tests_or_match ~term ~ty ~f = function
    | Tests l -> l |> List.map (fun (lhs,rhs) -> term lhs, f rhs) |> tests_
    | Match (m,missing) ->
      m
      |> ID.Map.map
        (fun (vars,rhs) -> List.map (Var.update_ty ~f:ty) vars, f rhs)
      |> match_ ~missing

  let rec map ~term ~ty t = match t with
    | Yield t -> yield (term t)
    | Cases cases ->
      let tests = map_tests_or_match cases.tests ~term ~ty ~f:(map ~term ~ty) in
      Cases {
        var=Var.update_ty ~f:ty cases.var;
        tests;
        default=CCOpt.map (map ~term ~ty) cases.default;
      }

  let rec filter_map ~test:ft ~yield:fy dt = match dt with
    | Yield t -> yield (fy t)
    | Cases {var; tests; default} ->
      let tests = match tests with
        | Match (m,missing) ->
          (* pass through *)
          ID.Map.map
            (fun (vars,rhs) -> vars, filter_map ~test:ft ~yield:fy rhs) m
          |> match_ ~missing
        | Tests l ->
          CCList.filter_map
            (fun (lhs,rhs) -> match ft var lhs with
               | None -> None
               | Some lhs' ->
                 Some (lhs', filter_map ~test:ft ~yield:fy rhs))
            l
          |> tests_
      and default =
        CCOpt.map (filter_map ~test:ft ~yield:fy) default
      in
      mk_cases var tests ~default

  let rec pp pt pty out t =
    let pp_default out = function
      | None -> ()
      | Some d -> fpf out ";@ default: %a" (pp pt pty) d
    in
    begin match t with
      | Yield t -> pt Precedence.Top out t
      | Cases {tests=Tests []; default=None; _} -> assert false
      | Cases {tests=Tests []; var; default=Some d} ->
        fpf out "@[<hv1>cases (@[%a:%a@])@ {default: %a@,}@]"
          Var.pp_full var pty (Var.ty var) (pp pt pty) d
      | Cases ({tests=Tests l; _} as cases) ->
        let pp_test out (lhs,rhs) =
          fpf out "@[<2>@[%a@] =>@ %a@]" (pt Precedence.Arrow) lhs (pp pt pty) rhs
        and pp_default out = function
          | None -> ()
          | Some d -> fpf out ";@ default: %a" (pp pt pty) d
        in
        let pp_tests = Utils.pp_list ~sep:"; " pp_test in
        fpf out "@[<hv1>cases (@[%a:%a@])@ {@[<v>%a%a@]@,}@]"
          Var.pp_full cases.var pty (Var.ty cases.var)
          pp_tests l pp_default cases.default
      | Cases ({tests=Match (m,_); _} as cases) ->
        let pp_branch out (id,(vars,rhs)) =
          fpf out "{@[<2>@[%a %a@] ->@ %a@]}"
            ID.pp id
            (Utils.pp_list ~sep:" " Var.pp_full) vars (pp pt pty) rhs
        in
        let pp_m out m = Utils.pp_seq ~sep:"; " pp_branch out (ID.Map.to_seq m) in
        fpf out "@[<hv1>cases (@[%a:%a@])@ {@[<v>%a%a@]@,}@]"
          Var.pp_full cases.var pty (Var.ty cases.var)
          pp_m m pp_default cases.default
    end

  let rec vars = function
    | Yield _ -> []
    | Cases {tests=Tests []; default=None; _} -> assert false
    | Cases {var; tests=Tests ((_,sub)::_); _} -> var :: vars sub
    | Cases {var; default=Some d; _} -> var :: vars d
    | Cases {tests=Match (m,_); default=None; _} when ID.Map.is_empty m -> assert false
    | Cases {var; tests=Match (m,_); _} ->
      let _, (_,rhs) = ID.Map.choose m in
      var :: vars rhs

  let ty_args dt = vars dt |> List.map Var.ty

  let num_vars dt = vars dt |> List.length

  let rec add_default t dt = match dt with
    | Yield _ -> dt
    | Cases {var; tests; default} ->
      let tests =
        map_tests_or_match tests ~f:(add_default t)
          ~ty:CCFun.id ~term:CCFun.id
      in
      let default = match default with
        | None ->
          (* add default case *)
          let d = match vars dt with
            | [] -> yield t
            | _ :: next_vars -> const next_vars (yield t)
          in
          Some d
        | Some _ as d -> d
      in
      mk_cases var tests ~default

  (** A test for the flat model *)
  type ('t, 'ty) flat_test = {
    ft_var: 'ty Var.t;
    ft_term: 't;
  }

  (** A flat model *)
  type ('t, 'ty) flat_dt = {
    fdt_vars: 'ty Var.t list;
    fdt_cases: (('t, 'ty) flat_test list * 't) list;
    fdt_default: 't option;
  }

  let mk_flat_test v t = {ft_var=v; ft_term=t}

  exception Unflattenable

  let flatten t : (_,_) flat_dt =
    let rec aux t : ((_,_) flat_test list * 't) Sequence.t = match t with
      | Yield t -> Sequence.return ([], t)
      | Cases {tests=Match _; _} -> raise Unflattenable
      | Cases {var; tests=Tests l; default} ->
        let sub_tests =
          l
          |> Sequence.of_list
          |> Sequence.flat_map
            (fun (lhs, rhs) ->
               aux rhs
               |> Sequence.map
                 (fun (tests,ret) -> {ft_var=var; ft_term=lhs} :: tests, ret))
        and sub_default = match default with
          | None -> Sequence.empty
          | Some d -> aux d
        in
        Sequence.append sub_tests sub_default
    in
    let l =
      aux t
      |> Sequence.to_rev_list
    in
    let fdt_vars = vars t in
    match l with
      | [] -> assert false
      | ([], d) :: tail ->
        { fdt_vars; fdt_cases=tail; fdt_default=Some d}
      | (_::_,_) :: _ ->
        (* no default *)
        { fdt_vars; fdt_cases=l; fdt_default=None }

  (* check invariants *)
  let check_ t =
    (* how to fail *)
    let pp_ =
      let pterm _ out _ = CCFormat.string out "<term>" in
      let pty out _ = CCFormat.string out "<ty>" in
      pp pterm pty
    in
    let fail_var v dt =
      Utils.failwithf "var %a@ does not match %a" Var.pp_full v pp_ dt
    and fail_vars v v' dt =
      Utils.failwithf "var %a and %a@ do not match in %a"
        Var.pp_full v Var.pp_full v' pp_ dt
    and fail_fun dt =
      Utils.failwithf "unexpected function@ %a" pp_ dt
    in
    let rec check_vars vars dt = match vars, dt with
      | [], Yield _ -> ()
      | v::_, Yield _ -> fail_var v dt
      | [], Cases _ -> fail_fun dt
      | v::vars', Cases {var; tests; default} ->
        if not (Var.equal v var) then fail_vars v var dt;
        begin match tests with
          | Tests l -> List.iter (fun (_,rhs) -> check_vars vars' rhs) l
          | Match (m,_) -> ID.Map.iter (fun _ (_,rhs) -> check_vars vars' rhs) m
        end;
        CCOpt.iter (check_vars vars') default;
    in
    check_vars (vars t) t

  (* recursively build a decision tree on the given list of variables *)
  let of_flat (type a) ~equal ~hash fdt =
    let module TTbl = CCHashtbl.Make(struct
        type t = a
        let equal = equal
        let hash = hash
      end)
    in
    let rec aux fdt = match fdt.fdt_vars with
      | [] ->
        begin match fdt.fdt_cases with
          | [] ->
            begin match fdt.fdt_default with
              | None -> invalid_arg "DT.of_flat: no case, no default"
              | Some d -> yield d
            end
          | ([], rhs) :: _ -> yield rhs (* TODO: warning if several cases? *)
          | (_::_, _) :: _ -> assert false
        end
      | v :: vars' ->
        (* partition [tests] around their value for [var] *)
        let by_term_tbl = TTbl.create 16 in
        (* other: cases that do not test on [var] *)
        let others =
          List.fold_left
            (fun others (eqns, value) ->
               match
                 CCList.find_idx
                   (fun {ft_var=v'; _} -> Var.equal v v')
                   eqns
               with
                 | None -> (eqns, value) :: others
                 | Some (i, {ft_term=t; _}) ->
                   let eqns' = CCList.remove_at_idx i eqns in
                   TTbl.add_list by_term_tbl t (eqns', value);
                   others)
            []
            fdt.fdt_cases
        in
        let tests =
          TTbl.to_seq by_term_tbl
          |> Sequence.map
            (fun (lhs, sub_tests) ->
               assert (sub_tests<>[]);
               let fdt' = { fdt with fdt_vars=vars'; fdt_cases=sub_tests} in
               lhs, aux fdt')
          |> Sequence.to_list
        in
        let default' = match others, fdt.fdt_default with
          | [], None -> None
          | _ ->
            let fdt' = {fdt with fdt_vars=vars'; fdt_cases=others} in
            Some (aux fdt')
        in
        mk_tests v ~tests ~default:default'
    in
    let res = aux fdt in
    check_ res;
    res

  let to_sexp ft fty t : Sexp_lib.t =
    let lst = Sexp_lib.list in
    let str = Sexp_lib.atom in
    let eqn_to_sexp {ft_var=v; ft_term=t} =
      lst [str "="; str (Var.to_string_full v); ft t]
    in
    let eqns_to_sexp = function
      | [] -> str "true"
      | [e] -> eqn_to_sexp e
      | l -> lst (str "and" :: List.map eqn_to_sexp l)
    in
    (* flatten into a single if/then/else *)
    let fdt = flatten t in
    (* caution: order matters (here [l] is reversed) *)
    let mk_ite l else_ =
      List.fold_left
        (fun else_ (eqns, then_) ->
           lst [str "if"; eqns_to_sexp eqns; ft then_; else_])
        else_ l
    and mk_fun vars body =
      List.fold_right
        (fun v body ->
           lst [str "fun";
                lst [str (Var.to_string_full v); fty (Var.ty v)];
                body])
        vars body
    in
    match fdt.fdt_default, List.rev fdt.fdt_cases with
      | Some d, l -> mk_fun fdt.fdt_vars (mk_ite l (ft d))
      | None, ((eqns, rhs) :: tail) ->
        (* last "if" has no "else" *)
        let d = lst [str "if"; eqns_to_sexp eqns; ft rhs] in
        mk_fun fdt.fdt_vars (mk_ite tail d)
      | None, [] -> assert false

  let pp_flat_test pt out {ft_var=v; ft_term=t} =
    fpf out "@[%a = %a@]" Var.pp_full v (pt Precedence.Eq) t

  let pp_flat pt out fdt =
    let pplist ~sep pp = Utils.pp_list ~sep pp in
    let pp_case out (tests,rhs) =
      fpf out "@[<2>(@[%a@]) =>@ %a@]"
        (pplist ~sep:" && " (pp_flat_test pt)) tests (pt Precedence.Arrow) rhs
    and pp_default out = function
      | None -> ()
      | Some d -> fpf out ",@ default=%a" (pt Precedence.App) d
    in
    let pp_cases = pplist ~sep:"" pp_case in
    fpf out "{@[<hv1>vars=(@[%a@]),@ tests=[@[<v>%a@]]%a@,@]}"
      (pplist ~sep:" " Var.pp_full) fdt.fdt_vars
      pp_cases fdt.fdt_cases
      pp_default fdt.fdt_default
end

module DT_util = struct
  module T = TermInner.Default
  module U = T.U
  module P = T.P

  type term = T.t
  type dt = (T.t, T.t) DT.t
  type subst = (T.t, T.t) Var.Subst.t

  let ite v ~then_ ~else_ =
    DT.mk_tests v ~tests:[U.true_, then_; U.false_, else_] ~default:None

  let rec eval_subst ~subst = function
    | DT.Yield t -> DT.yield (U.eval ~subst t)
    | DT.Cases {DT.var; tests; default} ->
      (* some variables are renamed (those introduced by a [match] branch),
         some other aren't *)
      let var' = match Var.Subst.find ~subst var with
        | None -> var
        | Some t ->
          begin match T.repr t with
            | TI.Var v' ->  v'
            | _ -> assert false
          end
      and tests = match tests with
        | DT.Tests l ->
          l
          |> List.map
            (fun (lhs,rhs) -> U.eval ~subst lhs, eval_subst ~subst rhs)
          |> DT.tests_
        | DT.Match (m,missing) ->
          m
          |> ID.Map.map
            (fun (vars, rhs) ->
               let subst, vars = CCList.fold_map U.rename_var subst vars in
               vars, eval_subst ~subst rhs)
          |> DT.match_ ~missing
      in
      let default = CCOpt.map (eval_subst ~subst) default in
      DT.mk_cases var' tests ~default

  let rec map_vars ~subst = function
    | DT.Yield t -> DT.yield (U.eval_renaming ~subst t)
    | DT.Cases {DT.var; tests; default} ->
      let var = Subst.find_or ~default:var ~subst var in
      let tests = match tests with
        | DT.Tests l ->
          l
          |> List.map
            (fun (lhs,rhs) -> U.eval_renaming ~subst lhs, map_vars ~subst rhs)
          |> DT.tests_
        | DT.Match (m,missing) ->
          m
          |> ID.Map.map
            (fun (vars,rhs) ->
               let subst, vars = CCList.fold_map Subst.rename_var subst vars in
               vars, map_vars ~subst rhs)
          |> DT.match_ ~missing
      in
      let default = CCOpt.map (map_vars ~subst) default in
      DT.mk_cases var tests ~default

  let rename_vars dt = eval_subst ~subst:Subst.empty dt

  exception Case_not_found of T.t

  let () = Printexc.register_printer
      (function
        | Case_not_found t ->
          Some (Utils.err_sprintf "case not found: `%a`" P.pp t)
        | _ -> None)

  let find_cases ?(subst=Subst.empty) t cases =
    let var = cases.DT.var in
    let default = cases.DT.default in
    (* look in if-based tests *)
    let find_tests_ tests =
      let subst = Subst.add ~subst var t in
      (* search for a matching case *)
      CCList.find_map
        (fun (lhs,rhs) ->
           if U.equal_with ~subst t lhs
           then Some (subst, eval_subst ~subst rhs)
           else None)
        tests
    (* lookup in match *)
    and find_match_ m = match U.app_const_unfold t with
      | None -> None
      | Some (id, args) ->
        begin match ID.Map.get id m with
          | None -> None
          | Some (vars, rhs) ->
            (* found the appropriate branch, bind [vars] and recurse in [rhs] *)
            assert (List.length vars = List.length args);
            let subst = Subst.add ~subst var t in
            let subst = Subst.add_list ~subst vars args in
            Some (subst, eval_subst ~subst rhs)
        end
    in
    let find_specific = match cases.DT.tests with
      | DT.Tests l -> find_tests_ l
      | DT.Match (m,_) -> find_match_ m
    in
    begin match find_specific, default with
      | Some c, _ -> c
      | None, Some d -> subst, d
      | None, None -> raise (Case_not_found t)
    end

  let apply_l (dt:dt) (args:T.t list): dt =
    let rec aux ~subst dt args = match dt, args with
      | _, [] -> eval_subst ~subst dt
      | DT.Yield _, _::_ -> invalid_arg "DT_util.apply: not a fun"
      | DT.Cases cases, arg :: args' ->
        let subst, case = find_cases ~subst arg cases in
        aux ~subst case args'
    in
    aux ~subst:Subst.empty dt args

  let apply dt arg = apply_l dt [arg]

  let rec join a b = match a with
    | DT.Yield t -> apply b t
    | DT.Cases {DT.var; tests; default} ->
      let tests =
        DT.map_tests_or_match tests
          ~f:(fun sub -> join sub b) ~ty:CCFun.id ~term:CCFun.id
      and default =
        CCOpt.map (fun d -> join d b) default
      in
      DT.mk_cases var tests ~default


  let is_tests_ = function
    | DT.Cases {DT.tests=DT.Tests _;_} -> true
    | _ -> false

  let is_match_ = function
    | DT.Cases {DT.tests=DT.Match _;_} -> true
    | _ -> false

  (* intersection *)
  let merge_missing =
    ID.Map.merge
      (fun _ a b -> match a, b with
         | Some i, Some j -> assert (i=j); Some i
         | _ -> None)

  (* merge a list of cases *)
  let rec merge_rec_l : ((_,_)DT.t * (_,_)Subst.t) list -> (_,_)DT.t = function
    | [] -> invalid_arg "DT_util.merge_l: empty list"
    | [t, subst] ->
      eval_subst ~subst t (* no need to merge *)
    | (DT.Yield _ as res, subst) :: _ ->
      eval_subst ~subst res (* arbitrary choice for leaves… *)
    | ((DT.Cases {DT.var; _}, _) :: _) as l ->
      if List.for_all (fun (x,_) -> is_tests_ x) l
      then merge_tests_ l
      else if List.for_all (fun (x,_) -> is_match_ x) l
      then merge_match_ l
      else (
        Utils.invalid_argf "DT_util.merge_l: mixed match/tests on `%a`"
          Var.pp_full var
      )

  (* merge the default-subtree, if any *)
  and merge_default (l:((_,_)DT.t * (_,_)Subst.t) list) : (_,_)DT.t option =
    let l =
      CCList.filter_map
        (fun (c,subst) -> match c with
           | DT.Yield _ -> assert false
           | DT.Cases {DT.default; _} -> CCOpt.map (fun x->x,subst) default)
        l
    in
    begin match l with
      | [] -> None
      | [d,subst] -> Some (eval_subst ~subst d)
      | _ -> Some (merge_rec_l l)
    end

  (* merging when all decision nodes are "tests" *)
  and merge_tests_ l : (_,_) DT.t = match l with
    | (DT.Cases {DT.var; tests=DT.Tests tests; _}, subst) :: tail ->
      let module TTbl = U.Tbl in
      let tbl : ((_,_) DT.t * (_,_)Subst.t) list TTbl.t = TTbl.create 32 in
      (* add one case to the table *)
      let merge_into_tbl subst (lhs,rhs) =
        TTbl.add_list tbl lhs (rhs,subst)
      in
      List.iter (merge_into_tbl subst) tests;
      (* now merge [tail] into [tbl] *)
      List.iter
        (function
          | DT.Yield _, _
          | DT.Cases {DT.tests=DT.Match _;_}, _ -> assert false
          | DT.Cases {DT.var=v'; tests=DT.Tests t'; _}, subst ->
            assert (Var.equal var v');
            List.iter (merge_into_tbl subst) t')
        tail;
      (* now build new cases *)
      let tests =
        TTbl.to_seq tbl
        |> Sequence.map
          (fun (t, sub_l) ->
             assert (sub_l <> []);
             t, merge_rec_l sub_l)
        |> Sequence.to_list
      and default =
        merge_default l
      in
      DT.mk_tests var ~tests ~default
    | _ -> assert false

  and merge_match_ l : (_,_)DT.t = match l with
    | (DT.Cases {DT.var; tests=DT.Match (m,missing0); _}, subst) :: tail ->
      (* add one case to the map *)
      let merge_into_map subst id (vars,rhs) m =
        let id_l = ID.Map.get_or id m ~default:[] in
        ID.Map.add id ((vars,rhs,subst)::id_l) m
      in
      let m0 = ID.Map.map (fun (vars,rhs) -> [vars,rhs,subst]) m in
      (* now merge [tail] into [tbl] *)
      let new_m, new_missing =
        List.fold_left
          (fun (m,missing) sub -> match sub with
             | DT.Yield _, _
             | DT.Cases {DT.tests=DT.Tests _;_}, _ -> assert false
             | DT.Cases {DT.var=v'; tests=DT.Match (m',missing'); _}, subst ->
               assert (Var.equal var v');
               let new_m = ID.Map.fold (merge_into_map subst) m' m in
               new_m, merge_missing missing missing')
          (m0,missing0)
          tail
      in
      let new_m =
        ID.Map.map
          (fun subs -> match subs with
             | [] -> assert false
             | (vars,rhs,subst) :: tail ->
               assert (List.for_all (fun v->not (Subst.mem ~subst v)) vars);
               (* rename variables in [tail] into [vars], all of
                  them are going to live under the same case [cstor vars -> …] *)
               let tail' =
                 let tvars = List.map U.var vars in
                 List.map
                   (fun (vars',rhs',subst') ->
                      assert (List.length vars = List.length vars');
                      let subst' = Subst.add_list ~subst:subst' vars' tvars in
                      rhs',subst')
                   tail
               in
               let new_rhs = merge_rec_l ((rhs,subst)::tail') in
               vars, new_rhs)
          new_m
      and default =
        merge_default l
      in
      (* now build new cases *)
      DT.mk_match var ~by_cstor:new_m ~missing:new_missing ~default
    | _ -> assert false

  let merge_l l =
    l
    |> List.map (fun dt -> dt, Subst.empty)
    |> merge_rec_l

  let merge a b = merge_l [a;b]

  (* is [l1] a permutation of [l2]? *)
  let is_perm_ l1 l2 : bool =
    let l1 = List.sort Var.compare l1 in
    let l2 = List.sort Var.compare l2 in
    CCList.equal Var.equal l1 l2

  let reorder vars dt =
    (* go through the flat form *)
    let fdt = DT.flatten dt in
    (* check *)
    let cur_vars = fdt.DT.fdt_vars in
    if not (is_perm_ vars cur_vars) then invalid_arg "DT_util.reorder";
    (* un-flatten in a different order *)
    let fdt' = {fdt with DT.fdt_vars=vars} in
    DT.of_flat ~equal:U.equal ~hash:U.hash fdt'

  let remove_vars vars dt =
    let rec aux subst vars dt = match dt with
      | DT.Yield t ->
        assert (vars=[]);
        DT.yield (U.eval ~subst t)
      | DT.Cases {DT.tests=DT.Match _; var; _} ->
        (* TODO: maybe in some cases we can push the matching in the "yield"? *)
        Utils.invalid_argf
          "remove_vars: cannot remove `%a`,@ used in match" Var.pp_full var
      | DT.Cases {DT.var=v; tests=DT.Tests l; default} ->
        if CCList.mem ~eq:Var.equal v vars
        then (
          let vars' = CCList.remove_one ~eq:Var.equal v vars in
          (* merge the sub-trees *)
          let l =
            List.map
              (fun (lhs,rhs) ->
                 let subst' = Subst.add ~subst v (U.eval ~subst lhs) in
                 aux subst' vars' rhs)
              l
          in
          (* add the default case, if needed *)
          let l =
            let default = CCOpt.map (aux subst vars') default in
            CCList.cons_maybe default l
          in
          assert (l<>[]);
          merge_l l
        ) else (
          let l =
            List.map
              (fun (lhs,rhs) ->
                 U.eval ~subst lhs, aux subst vars rhs)
              l
          and default =
            CCOpt.map (aux subst vars) default
          in
          DT.mk_tests v ~tests:l ~default
        )
    in
    (* remove duplicates *)
    let vars = CCList.sort_uniq ~cmp:Var.compare vars in
    (* check that [vars] subset of current set of vars *)
    let cur_vars = DT.vars dt in
    if not (List.for_all (fun x->CCList.mem ~eq:Var.equal x cur_vars) vars)
    then invalid_arg "DT_util.remove_vars";
    aux Subst.empty vars dt

  let remove_first_var dt = match DT.vars dt with
    | [] -> invalid_arg "DT_util.remove_first_var: constant tree"
    | v :: _ -> remove_vars [v] dt

  let to_term dt: T.t =
    let vars = DT.vars dt in
    (* make the nested-if tree *)
    let rec aux dt = match dt with
      | DT.Yield t -> t
      | DT.Cases {DT.tests=DT.Tests []; default=None; _} -> assert false
      | DT.Cases {DT.tests=DT.Tests []; default=Some d; _} -> aux d
      | DT.Cases {DT.var; tests=DT.Tests l; default=Some d} ->
        let default = aux d in
        aux_ite_l var l default
      | DT.Cases {DT.var; tests=DT.Tests l; default=None} ->
        (* NOTE: it would be better to have some "unreachable" here, but we
           do not have the return type *)
        let last = match List.rev l with (_,t)::_ -> t | []-> assert false in
        aux_ite_l var l (aux last)
      | DT.Cases {DT.tests=DT.Match (m,_); default=None; _} when ID.Map.is_empty m ->
        assert false
      | DT.Cases {DT.tests=DT.Match (m,missing); default; var} ->
        let m =
          ID.Map.map
            (fun (vars,rhs) -> vars, aux rhs)
            m
        and default = match default with
          | None -> TI.Default_none
          | Some rhs ->
            TI.Default_some (aux rhs, missing)
        in
        U.match_with (U.var var) m ~def:default

    (* make a if/then/else tree *)
    and aux_ite_l var l default =
      List.fold_right
        (fun (lhs,rhs) else_ ->
           let then_ = aux rhs in
           (* eliminate redundancies: [if a b b --> b] *)
           if U.equal then_ else_ then else_
           else U.ite (U.eq (U.var var) lhs) then_ else_
        )
        l default
    in
    U.fun_l vars (aux dt)

  let pp : dt printer = DT.pp P.pp' P.pp
end

(** {2 Models} *)

type symbol_kind =
  | Symbol_prop
  | Symbol_fun
  | Symbol_utype
  | Symbol_data
  | Symbol_codata

type (+'t, +'ty) value_def = 't * ('t, 'ty) DT.t * symbol_kind

(** A model *)
type (+'t, +'ty) t = {
  values: ('t, 'ty) value_def list;
  (* term -> its interpretation *)

  finite_types: ('ty * ID.t list) list;
  (* type -> finite domain *)

  potentially_spurious: bool;
  (** the model might be spurious, i.e. some approximation made the
        translation unsound *)
}

type ('a,'b) model = ('a,'b) t

let empty = {
  values=[];
  finite_types=[];
  potentially_spurious=false;
}

let empty_copy m = { empty with potentially_spurious = m.potentially_spurious; }

let add_const m (t,u,k) =
  {m with values = (t,DT.yield u,k) :: m.values; }

let add_value t f = {t with values = f :: t.values; }

let add_finite_type t ty dom =
  {t with finite_types = (ty, dom) :: t.finite_types; }

let values m = m.values |> Sequence.of_list
let finite_types m = m.finite_types |> Sequence.of_list

let map ~term:fterm ~ty:fty m = {
  m with
    values=CCList.map
        (fun (t,dt,k) ->
           fterm t, DT.map ~term:fterm ~ty:fty dt, k)
        m.values;
    finite_types=List.map (fun (ty,l) -> fty ty, l) m.finite_types;
}

let filter_map ~values ~finite_types m = {
  m with
    values = CCList.filter_map values m.values;
    finite_types = CCList.filter_map finite_types m.finite_types;
}

let const_true_ _ = true
let const_unit_ _ = ()
let const_fst_ x _ = x

let filter
    ?(values=const_true_)
    ?(finite_types=const_true_)
    m
  =
  filter_map m
    ~values:(fun x -> if values x then Some x else None)
    ~finite_types:(fun x -> if finite_types x then Some x else None)

let iter ?(values=const_unit_) ?(finite_types=const_unit_) m =
  List.iter values m.values;
  List.iter finite_types m.finite_types;
  ()

let fold ?(values=const_fst_) ?(finite_types=const_fst_) acc m =
  let acc = ref acc in
  iter m
    ~values:(fun x -> acc := values !acc x)
    ~finite_types:(fun x -> acc := finite_types !acc x);
  !acc

let pp pt pty out m =
  let pplist ~sep pp = Utils.pp_list ~sep pp in
  let pp_type out (ty,dom) =
    fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]."
      pty ty (pplist ~sep:", " ID.pp) dom
  and pp_value out (t,dt,_) =
    fpf out "@[<2>val @[%a@]@ :=@ %a@]."
      (pt Precedence.Top) t
      (DT.pp pt pty) dt
  in
  (* only print non-empty lists *)
  let pp_nonempty_list pp out l =
    if l=[] then ()
    else fpf out "@[<v>%a@]@," (pplist ~sep:"" pp) l
  in
  fpf out "@[<v>%a%a@]"
    (pp_nonempty_list pp_type) m.finite_types
    (pp_nonempty_list pp_value) m.values

let str = Sexp_lib.atom
let lst = Sexp_lib.list

let to_sexp ft fty m : Sexp_lib.t =
  let id_to_sexp id = str (ID.to_string id) in
  let ty_to_sexp (ty,dom) =
    lst [str "type"; fty ty; lst (List.map id_to_sexp dom)] in
  let value_to_sexp (t,dt,_) =
    let fun_ = DT.to_sexp ft fty dt in
    lst [str "val"; ft t; fun_]
  in
  lst
    ( List.map ty_to_sexp m.finite_types
      @ List.map value_to_sexp m.values)

module Default = struct
  module T = TermInner.Default
  module P = T.P

  type term = T.t
  type t = (T.t, T.t) model

  let to_sexp = to_sexp P.to_sexp P.to_sexp

  type simple_atom =
    | SA_ty of T.t * ID.t list
    | SA_val of T.t * T.t

  (* a "simple" model *)
  type simple = simple_atom list

  let to_simple (m:t) : simple =
    fold [] m
      ~finite_types:(fun acc (ty,ids) -> SA_ty (ty,ids) :: acc)
      ~values:(fun acc (t,dt,_) ->
        SA_val (t, DT_util.to_term dt) :: acc)

  let pplist ~sep pp = Utils.pp_list ~sep pp

  let pp_simple_atom out = function
    | SA_ty (ty,dom) ->
      fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]."
        P.pp ty (pplist ~sep:", " ID.pp) dom
    | SA_val (t,u) ->
      fpf out "@[<2>val @[%a@]@ :=@ %a@]."
        P.pp t (P.pp' Precedence.Arrow) u

  let pp_simple out = fpf out "@[<v>%a@]" (pplist ~sep:"" pp_simple_atom)

  let pp_standard out m =
    let s = to_simple m in
    pp_simple out s
end
