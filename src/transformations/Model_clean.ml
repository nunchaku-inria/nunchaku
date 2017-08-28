
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Rename values in a model} *)

open Nunchaku_core

module TI = TermInner
module M = Model
module DT = Model.DT
module T = TermInner.Default
module U = T.U
module P = T.P
module Ty = TypeMono.Make(T)
module Red = Reduce.Make(T)

type term = T.t
type model = (T.t, T.t) Model.t

let fpf = Format.fprintf
let name = "model_clean"
let section = Utils.Section.(make ~parent:root) name

(* a kind of flat-form printing of [t] *)
let rec flatten_ty out t = match T.repr t with
  | TI.App (f,l) ->
    fpf out "%a_%a"
      flatten_ty f
      (Utils.pp_list ~sep:"_" flatten_ty) l
  | TI.Const id -> ID.pp_name out id
  | TI.TyBuiltin b -> CCFormat.string out (TI.TyBuiltin.to_string b)
  | _ -> ()

(* return a prefix for constants in the domain of this given type *)
let pick_prefix_ ty = CCFormat.sprintf "@[<h>%a@]" flatten_ty ty

(* compute a set of renaming rules for the model [m] *)
let renaming_rules_of_model_ m =
  List.fold_left
    (fun acc (t, dom) ->
       let prefix = pick_prefix_ t in
       CCList.foldi
         (fun acc i id ->
            let name = CCFormat.sprintf "$%s_%d" prefix i in
            let rhs = ID.fresh_copy_name id name in
            ID.Map.add id rhs acc)
         acc dom)
    ID.Map.empty
    m.Model.finite_types

type rules = ID.t ID.Map.t

let pp_rule_ out (l,r) =
  fpf out "%a → @[%a@]" ID.pp l ID.pp r

let rename_ i v =
  let name = Format.sprintf "v_%d" i in
  Var.make ~ty:(Var.ty v) ~name

(* rename [v] and add the renaming to [subst] *)
let rename_copy_ subst v =
  let v' = rename_ (Var.Subst.size subst) v in
  Var.Subst.add ~subst v v', v'

(* rewrite [t] using the set of rewrite rules *)
let rec rewrite_term_ (rules:rules) subst t : T.t = match T.repr t with
  | TI.Const id ->
    begin match ID.Map.get id rules with
      | Some id' -> U.const id'
      | None -> t
    end
  | TI.Var v ->
    begin try U.var (Var.Subst.find_exn ~subst v)
      with Not_found -> t
    end
  | _ ->
    let t =
      U.map subst t
        ~f:(rewrite_term_ rules)
        ~bind:rename_copy_
    in
    (* reduce the term *)
    Red.whnf t

let rename m : (_,_) Model.t =
  let rules = renaming_rules_of_model_ m in
  Utils.debugf 5 ~section "@[<2>apply rewrite rules@ @[<v>%a@]@]"
    (fun k->k (Utils.pp_seq ~sep:"" pp_rule_) (ID.Map.to_seq rules));
  (* update domains *)
  let finite_types =
    let rename_id id = ID.Map.get_or ~default:id id rules in
    List.map
      (fun (t, dom) -> t, List.map rename_id dom)
      m.Model.finite_types
  in
  (* rewrite every term *)
  let rw_nil = rewrite_term_ rules Var.Subst.empty in
  { m with Model.
        finite_types;
        values=List.map
            (fun (t,dt,k) ->
               let t = rw_nil t in
               let dt = DT.map ~term:rw_nil ~ty:rw_nil dt in
               let subst =
                 let vars = DT.vars dt in
                 let vars' = List.mapi rename_ vars in
                 Var.Subst.of_list vars vars'
               in
               let dt = M.DT_util.map_vars ~subst dt in
               t, dt, k
            )
            m.Model.values;
  }

let ground_dt doms (dt:(_,_) M.DT.t): (_,_) M.DT.t =
  let module D = M.DT in
  let rec ground_dt (subst:U.subst) dt = match dt with
    | D.Yield rhs -> D.yield (U.eval ~subst rhs)
    | D.Cases c ->
      let tests, changed = match c.D.tests with
        | D.Match (map,missing) ->
          let map = ID.Map.map (fun (vars,dt) -> vars, ground_dt subst dt) map in
          D.match_ ~missing map, false
        | D.Tests l when List.for_all (fun (t,_) -> not (U.is_var t)) l ->
          (* simple case where there are no variables *)
          let c =
            List.map (fun (t,dt) -> t, ground_dt subst dt) l
            |> D.tests_
          in
          c, false
        | D.Tests l ->
          (* there is at least one variable. We need to ground the variables
             and group sub-decision trees by corresponding LHS value *)
          let tbl = U.Tbl.create 16 in
          List.iter
            (fun c ->
               let l = ground_case subst c in
               List.iter (fun (t,dt) -> U.Tbl.add_list tbl t dt) l)
            l;
          (* now group again *)
          let l =
            U.Tbl.to_list tbl
            |> List.map
              (fun (t,dt_l) -> t, List.rev dt_l |> M.DT_util.merge_l)
          in
          D.tests_ l, true
      in
      let default = CCOpt.map (ground_dt subst) c.D.default in
      let dt' = D.mk_cases ~default c.D.var tests in
      if changed then (
        Utils.debugf ~section 5
          "(@[<hv2>ground_vars@ :dt %a@ :subst %a@ :into %a@])"
          (fun k->k M.DT_util.pp dt (Var.Subst.pp P.pp) subst M.DT_util.pp dt');
      );
      dt'

  (* expand case with variables into list of trees *)
  and ground_case subst ((t,dt):(_,_) D.case) : (_,_) D.case list =
    match T.repr t with
      | TI.Var v ->
        begin match U.Tbl.get doms (Var.ty v) with
          | Some dom ->
            (* testing on a variable ranging over domain of [Var.ty v] *)
            List.map
              (fun dom_id ->
                 let t' = U.const dom_id in
                 let subst = Var.Subst.add ~subst v t' in
                 t', ground_dt subst dt)
              dom
          | _ -> [t, ground_dt subst dt]
        end
      | _ -> [t, ground_dt subst dt]
  in
  ground_dt Var.Subst.empty dt

(* remove free variables whose types are finite domains *)
let ground_vars m : (_,_) Model.t =
  (* collect finite domains *)
  let doms_tbl = U.Tbl.create 16 in
  M.iter m
    ~finite_types:(fun (ty,dom) -> U.Tbl.add doms_tbl ty dom);
  (* now ground decision trees that contain free variables *)
  Model.filter_map m
    ~finite_types:CCOpt.return
    ~values:(fun (lhs,dt,k) ->
      let dt = ground_dt doms_tbl dt in
      Some (lhs,dt,k))

(* remove recursion in models *)
let remove_recursion m : (_,_) Model.t =
  let rec eval_t t : T.t = match T.repr t with
    | TI.App(_,[]) -> assert false
    | TI.App(f, l) ->
      let l = List.map eval_t l in
      begin match T.repr f with
        | TI.Const id ->
          let res =
            CCList.find_map
              (fun (lhs,dt,_) -> match T.repr lhs with
                 | TI.Const id' when ID.equal id id' ->
                   assert (DT.num_vars dt >= List.length l);
                   Some dt
                 | _ -> None)
              m.Model.values
          in
          begin match res with
            | None -> U.app f l
            | Some dt ->
              let dt' = M.DT_util.apply_l dt l in
              Utils.debugf ~section 5 "@[<2>eval `@[%a@]`@ into `@[%a@]`@]"
                (fun k->k P.pp t M.DT_util.pp dt');
              (* if there remain arguments, consider the [dt] as a function
                 anyway *)
              eval_t (M.DT_util.to_term dt')
          end
        | _ -> U.app f l
      end
    | _ -> t
  in
  Model.map m ~term:eval_t ~ty:(fun ty->ty)

(* remove trivial tests [x = x] *)
let remove_trivial_tests m : (_,_) Model.t =
  let rec aux dt = match dt with
    | DT.Yield _ -> dt
    | DT.Cases {DT.var; tests=DT.Tests l; default=d} ->
      let others, tests =
        CCList.fold_filter_map
          (fun o (lhs,rhs) ->
             let rhs = aux rhs in
             match T.repr lhs with
               | TI.Var v' when Var.equal var v' ->
                 rhs :: o, None
               | _ -> o, Some (lhs, rhs))
          [] l
      in
      (* if some tests became trivial, they might replace [default] *)
      let default = match d, others with
        | None, [] -> None
        | None, o1 :: _ -> Some o1
        | Some d, _ -> Some (aux d)
      in
      DT.mk_tests var ~tests ~default
    | DT.Cases {DT.var; tests=DT.Match (m,missing); default=d} ->
      let default = CCOpt.map aux d in
      let m = ID.Map.map (fun (vars,rhs) -> vars, aux rhs) m in
      DT.mk_match var ~by_cstor:m ~missing ~default
  in
  Model.filter_map m
    ~finite_types:(fun tup -> Some tup)
    ~values:(fun (t,dt,k) ->
      let dt = aux dt in
      Some (t,dt,k))

let pipe ~print:must_print =
  Transform.backward ~name
    (fun res ->
       let f m =
         m
         |> ground_vars
         |> remove_recursion
         |> remove_trivial_tests
         |> rename
       in
       let res' = Problem.Res.map_m ~f res in
       if must_print then (
         let module P = TI.Print(T) in
         Format.printf "@[<v2>@{<Yellow>res after %s@}:@ %a@]@."
           name (Problem.Res.pp P.pp' P.pp) res');
       res')
