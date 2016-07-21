(* This file is free software, part of nunchaku. See file "license" for more details. *)

module TI = TermInner
module Subst = Var.Subst

type 'a printer = Format.formatter -> 'a -> unit
type 'a prec_printer = TermInner.prec -> 'a printer
type 'a to_sexp = 'a -> CCSexp.t

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
  and ('t, 'ty) cases = {
    var: 'ty Var.t;
    (* the variable being tested *)
    tests: ('t, 'ty) case list;
    (* list of [if var=term, then sub-dt] *)
    default: ('t, 'ty) t option;
    (* sub-dt by default *)
  }

  and ('t, 'ty) case = 't * ('t, 'ty) t

  let yield t = Yield t

  let cases v ~tests ~default =
    if tests=[] && default=None then invalid_arg "DT.cases";
    Cases { var=v; tests; default; }

  let rec const vars ret = match vars with
    | [] -> ret
    | v :: vars' ->
      let default = Some (const vars' ret) in
      cases v ~tests:[] ~default

  let rec map ~term ~ty t = match t with
    | Yield t -> yield (term t)
    | Cases cases ->
      Cases {
        var=Var.update_ty ~f:ty cases.var;
        tests=
          List.map
            (fun (lhs,rhs) -> term lhs, map ~term ~ty rhs)
            cases.tests;
        default=CCOpt.map (map ~term ~ty) cases.default;
      }

  let rec filter_map ~test:ft ~yield:fy dt = match dt with
    | Yield t -> yield (fy t)
    | Cases {var; tests; default} ->
      let tests =
        CCList.filter_map
          (fun (lhs,rhs) -> match ft var lhs with
             | None -> None
             | Some lhs' ->
               Some (lhs', filter_map ~test:ft ~yield:fy rhs))
          tests
      and default =
        CCOpt.map (filter_map ~test:ft ~yield:fy) default
      in
      cases var ~tests ~default

  let rec print pt out t = match t with
    | Yield t -> pt TI.P_top out t
    | Cases {tests=[]; default=None; _} -> assert false
    | Cases {tests=[]; var; default=Some d} ->
      fpf out "@[<hv1>cases %a@ {default: %a@,}@]"
        Var.print_full var (print pt) d
    | Cases cases ->
      let pp_test out (lhs,rhs) =
        fpf out "@[<2>@[%a@] =>@ %a@]" (pt TI.P_arrow) lhs (print pt) rhs
      and pp_default out = function
        | None -> ()
        | Some d -> fpf out ";@ default: %a" (print pt) d
      in
      let pp_tests = CCFormat.list ~start:"" ~stop:"" ~sep:"; " pp_test in
      fpf out "@[<hv1>cases %a@ {@[<v>%a%a@]@,}@]"
        Var.print_full cases.var pp_tests cases.tests pp_default cases.default

  let rec ty_args = function
    | Yield _ -> []
    | Cases {tests=[]; default=None; _} -> assert false
    | Cases {var; tests=(_,sub)::_; _} -> Var.ty var :: ty_args sub
    | Cases {var; default=Some d; _} -> Var.ty var :: ty_args d

  let rec vars = function
    | Yield _ -> []
    | Cases {tests=[]; default=None; _} -> assert false
    | Cases {var; tests=(_,sub)::_; _} -> var :: vars sub
    | Cases {var; default=Some d; _} -> var :: vars d

  let num_vars dt = vars dt |> List.length

  let rec add_default t dt = match dt with
    | Yield _ -> dt
    | Cases {var; tests; default} ->
      let tests = List.map (fun (lhs,rhs) -> lhs, add_default t rhs) tests in
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
      cases var ~tests ~default

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

  let flatten t : _ flat_dt =
    let rec aux t : (_ flat_test list * 't) Sequence.t = match t with
      | Yield t -> Sequence.return ([], t)
      | Cases {var; tests; default} ->
        let sub_tests =
          tests
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
      print pterm
    in
    let fail_var v dt =
      Utils.failwithf "var %a@ does not match %a" Var.print_full v pp_ dt
    and fail_vars v v' dt =
      Utils.failwithf "var %a and %a@ do not match in %a"
        Var.print_full v Var.print_full v' pp_ dt
    and fail_fun dt =
      Utils.failwithf "unexpected function@ %a" pp_ dt
    in
    let rec check_vars vars dt = match vars, dt with
      | [], Yield _ -> ()
      | v::_, Yield _ -> fail_var v dt
      | [], Cases _ -> fail_fun dt
      | v::vars', Cases {var; tests; default} ->
        if not (Var.equal v var) then fail_vars v var dt;
        List.iter (fun (_,rhs) -> check_vars vars' rhs) tests;
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
                   let eqns' = CCList.Idx.remove eqns i in
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
        cases v ~tests ~default:default'
    in
    let res = aux fdt in
    check_ res;
    res

  let to_sexp ft t : CCSexp.t =
    let lst = CCSexp.of_list in
    let str = CCSexp.atom in
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
    in
    match fdt.fdt_default, List.rev fdt.fdt_cases with
      | Some d, l -> mk_ite l (ft d)
      | None, ((eqns, rhs) :: tail) ->
        (* last "if" has no "else" *)
        let d = lst [str "if"; eqns_to_sexp eqns; ft rhs] in
        mk_ite tail d
      | None, [] -> assert false

  let print_flat_test pt out {ft_var=v; ft_term=t} =
    fpf out "@[%a = %a@]" Var.print_full v (pt TI.P_eq) t

  let print_flat pt out fdt =
    let pplist ~sep pp = CCFormat.list ~start:"" ~stop:"" ~sep pp in
    let pp_case out (tests,rhs) =
      fpf out "@[<2>(@[%a@]) =>@ %a@]"
        (pplist ~sep:" && " (print_flat_test pt)) tests (pt TI.P_arrow) rhs
    and pp_default out = function
      | None -> ()
      | Some d -> fpf out ",@ default=%a" (pt TI.P_app) d
    in
    let pp_cases = pplist ~sep:"" pp_case in
    fpf out "{@[<hv1>vars=(@[%a@]),@ tests=[@[<v>%a@]]%a@,@]}"
      (pplist ~sep:" " Var.print_full) fdt.fdt_vars
      pp_cases fdt.fdt_cases
      pp_default fdt.fdt_default
end

module DT_util = struct
  module T = TermInner.Default
  module U = T.U
  module P = T.P

  type dt = (T.t, T.t) DT.t
  type subst = (T.t, T.t) Var.Subst.t

  let ite v ~then_ ~else_ =
    DT.cases v ~tests:[U.true_, then_; U.false_, else_] ~default:None

  let rec eval_subst ~subst = function
    | DT.Yield t -> DT.yield (U.eval ~subst t)
    | DT.Cases {DT.var; tests; default} ->
      assert (not (Subst.mem ~subst var));
      let tests =
        List.map
          (fun (lhs,rhs) -> U.eval ~subst lhs, eval_subst ~subst rhs)
          tests
      in
      let default = CCOpt.map (eval_subst ~subst) default in
      DT.cases var ~tests ~default

  let rec map_vars ~subst = function
    | DT.Yield t -> DT.yield (U.eval_renaming ~subst t)
    | DT.Cases {DT.var; tests; default} ->
      let var = Subst.find_or ~default:var ~subst var in
      let tests =
        List.map
          (fun (lhs,rhs) -> U.eval_renaming ~subst lhs, map_vars ~subst rhs)
          tests
      in
      let default = CCOpt.map (map_vars ~subst) default in
      DT.cases var ~tests ~default

  let rename_vars dt = eval_subst ~subst:Subst.empty dt

  exception Case_not_found of T.t

  let () = Printexc.register_printer
      (function
        | Case_not_found t ->
          Some (Utils.err_sprintf "case not found: `%a`" P.print t)
        | _ -> None)

  let find_cases ?(subst=Subst.empty) t cases =
    let {DT.var; tests; default} = cases in
    let subst = Subst.add ~subst var t in
    (* search for a matching case *)
    let case =
      CCList.find_map
        (fun (lhs,rhs) ->
           if U.equal_with ~subst t lhs
           then Some (eval_subst ~subst rhs)
           else None)
        tests
    in
    let case = match case, default with
      | Some c, _ -> c
      | None, Some d -> d
      | None, None -> raise (Case_not_found t)
    in
    subst, case

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
        List.map
          (fun (lhs, rhs) -> lhs, join rhs b)
          tests
      and default =
        CCOpt.map (fun d -> join d b) default
      in
      DT.cases var ~tests ~default

  let rec merge_l = function
    | [] -> invalid_arg "DT_util.merge_l"
    | [t] -> t
    | DT.Yield _ as res :: _ -> res (* arbitrary… *)
    | DT.Cases {DT.var; tests=t; default} :: tail ->
      let module TTbl = U.Tbl in
      let tbl : _ DT.t list TTbl.t = TTbl.create 32 in
      (* add one case to the table *)
      let merge_into_tbl (lhs,rhs) =
        TTbl.add_list tbl lhs rhs
      in
      List.iter merge_into_tbl t;
      (* now merge [tail] into [tbl] *)
      List.iter
        (function
          | DT.Yield _ -> assert false
          | DT.Cases {DT.var=v'; tests=t'; _} ->
            assert (Var.equal var v');
            List.iter merge_into_tbl t')
        tail;
      (* now build new cases *)
      let tests =
        TTbl.to_seq tbl
        |> Sequence.map
          (fun (t, sub_l) ->
             assert (sub_l <> []);
             t, merge_l sub_l)
        |> Sequence.to_list
      in
      DT.cases var ~tests ~default

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
      | DT.Cases {DT.var=v; tests; default} ->
        if CCList.Set.mem ~eq:Var.equal v vars
        then (
          let vars' = CCList.Set.remove ~eq:Var.equal v vars in
          (* merge the sub-trees *)
          let l =
            List.map
              (fun (lhs,rhs) ->
                 let subst' = Subst.add ~subst v (U.eval ~subst lhs) in
                 aux subst' vars' rhs)
              tests
          in
          (* add the default case, if needed *)
          let l =
            let default = CCOpt.map (aux subst vars') default in
            CCList.cons_maybe default l
          in
          assert (l<>[]);
          merge_l l
        )
        else (
          let tests =
            List.map
              (fun (lhs,rhs) ->
                 U.eval ~subst lhs, aux subst vars rhs)
              tests
          and default =
            CCOpt.map (aux subst vars) default
          in
          DT.cases v ~tests ~default
        )
    in
    (* remove duplicates *)
    let vars = CCList.sort_uniq ~cmp:Var.compare vars in
    (* check that [vars] subset of current set of vars *)
    let cur_vars = DT.vars dt in
    if not (List.for_all (fun x->CCList.Set.mem ~eq:Var.equal x cur_vars) vars)
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
      | DT.Cases {DT.tests=[]; default=None; _} -> assert false
      | DT.Cases {DT.tests=[]; default=Some d; _} -> aux d
      | DT.Cases {DT.var; tests; default=Some d} ->
        let default = aux d in
        aux_ite_l var tests default
      | DT.Cases {DT.var; tests; default=None} ->
        (* NOTE: it would be better to have some "unreachable" here, but we
           do not have the return type *)
        let last = match List.rev tests with (_,t)::_ -> t | []-> assert false in
        aux_ite_l var tests (aux last)
    (* make a if/then/else tree *)
    and aux_ite_l var l default =
      List.fold_right
        (fun (lhs,rhs) else_ ->
           U.ite (U.eq (U.var var) lhs)
             (aux rhs)
             else_)
        l default
    in
    U.fun_l vars (aux dt)

  let print : dt printer = DT.print P.print'
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

let print pt pty out m =
  let pplist ~sep pp = CCFormat.list ~sep ~start:"" ~stop:"" pp in
  let pp_type out (ty,dom) =
    fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]"
      pty ty (pplist ~sep:", " ID.print) dom
  and pp_value out (t,dt,_) =
    fpf out "@[<2>val @[%a@]@ :=@ %a@]."
      (pt TI.P_top) t
      (DT.print pt) dt
  in
  (* only print non-empty lists *)
  let pp_nonempty_list pp out l =
    if l=[] then ()
    else fpf out "@[<v>%a@]@," (pplist ~sep:"" pp) l
  in
  fpf out "@[<v>%a%a@]"
    (pp_nonempty_list pp_type) m.finite_types
    (pp_nonempty_list pp_value) m.values

let str = CCSexp.atom
let lst = CCSexp.of_list

let to_sexp ft fty m : CCSexp.t =
  let id_to_sexp id = str (ID.to_string id) in
  let ty_to_sexp (ty,dom) =
    lst [str "type"; fty ty; lst (List.map id_to_sexp dom)] in
  let value_to_sexp (t,dt,_) =
    let fun_ = DT.to_sexp ft dt in
    lst [str "val"; ft t; fun_]
  in
  lst
    ( List.map ty_to_sexp m.finite_types
    @ List.map value_to_sexp m.values)

module Default = struct
  module T = TermInner.Default
  module P = T.P

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

  let pplist ~sep pp = CCFormat.list ~sep ~start:"" ~stop:"" pp

  let pp_simple_atom out = function
    | SA_ty (ty,dom) ->
      fpf out "@[<2>type @[%a@]@ :=@ {@[<hv>%a@]}@]."
        P.print ty (pplist ~sep:", " ID.print) dom
    | SA_val (t,u) ->
      fpf out "@[<2>val @[%a@]@ :=@ %a@]."
        P.print t (P.print' TI.P_arrow) u

  let pp_simple out = fpf out "@[<v>%a@]" (pplist ~sep:"" pp_simple_atom)

  let print_standard out m =
    let s = to_simple m in
    pp_simple out s
end
