
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
      CCFormat.(list ~start:"" ~stop:"" ~sep:"_" flatten_ty) l
  | TI.Const id -> ID.print_name out id
  | TI.TyBuiltin b -> CCFormat.string out (TI.TyBuiltin.to_string b)
  | _ -> ()

(* return a prefix for constants in the domain of this given type *)
let pick_prefix_ ty = CCFormat.sprintf "@[<h>%a@]" flatten_ty ty

(* compute a set of renaming rules for the model [m] *)
let renaming_rules_of_model_ m =
  List.fold_left
    (fun acc (t, dom) ->
       let prefix = pick_prefix_ t in
       CCList.Idx.foldi
         (fun acc i id ->
            let name = CCFormat.sprintf "$%s_%d" prefix i in
            let rhs = ID.make name in
            ID.Map.add id rhs acc)
         acc dom)
    ID.Map.empty
    m.Model.finite_types

type rules = ID.t ID.Map.t

let pp_rule_ out (l,r) =
  fpf out "%a → @[%a@]" ID.print l ID.print r

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
    (fun k->k (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_rule_) (ID.Map.to_seq rules));
  (* update domains *)
  let finite_types =
    let rename_id id = ID.Map.get_or ~or_:id id rules in
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
                (fun k->k P.print t M.DT_util.print dt');
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
    | DT.Cases {DT.var; tests; default=d} ->
      let others, tests =
        CCList.fold_filter_map
          (fun o (lhs,rhs) ->
             let rhs = aux rhs in
             match T.repr lhs with
               | TI.Var v' when Var.equal var v' ->
                 rhs :: o, None
               | _ -> o, Some (lhs, rhs))
          [] tests
      in
      (* if some tests became trivial, they might replace [default] *)
      let default = match d, others with
        | None, [] -> None
        | None, o1 :: _ -> Some o1
        | Some d, _ -> Some (aux d)
      in
      DT.cases var ~tests ~default
  in
  Model.filter_map m
    ~finite_types:(fun tup -> Some tup)
    ~values:(fun (t,dt,k) ->
      let dt = aux dt in
      Some (t,dt,k))

let pipe ~print:must_print =
  Transform.backward ~name
    (fun res ->
       let f m = m |> remove_recursion |> remove_trivial_tests |> rename in
       let res' = Problem.Res.map_m ~f res in
       if must_print then (
         let module P = TI.Print(T) in
         Format.printf "@[<v2>@{<Yellow>after model %s@}:@ %a@]@."
           name (Problem.Res.print P.print' P.print) res');
       res')
