
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = Term
module Pol = Polarity
module AT = AnalyzeType.Make(T)
module TyTbl = T.Tbl

let name = "elim_copy"
let section = Utils.Section.make name

type term = T.t
type ty = T.t

type state = {
  env: (term, ty) Env.t;
  incomplete_types: unit TyTbl.t; (* copy types that are incomplete (missing elements) *)
  abstract_types: unit TyTbl.t; (* copy types that are abstract (confusion among elements) *)
  copy_as_uninterpreted: unit ID.Tbl.t; (* copy types mapped to uninterpreted types *)
  at_cache: AT.cache;
  mutable unsat_means_unknown: bool;
}

type decode_state = state

let create_state ~env = {
  env;
  at_cache=AT.create_cache ();
  incomplete_types=TyTbl.create 16;
  abstract_types=TyTbl.create 16;
  copy_as_uninterpreted=ID.Tbl.create 16;
  unsat_means_unknown=false;
}

let error msg = failwith ("in " ^ name ^ ": " ^ msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

(** {2 Encoding} *)

(* encode the copy type as a datatype *)
let copy_as_data ~info (c:(_,_) Stmt.copy): (_,_) Stmt.t list =
  (* the datatype itself, whose cstor is [c.copy_abstract] *)
  let cstor =
    { Stmt.
      cstor_name = c.Stmt.copy_abstract;
      cstor_args = [c.Stmt.copy_of];
      cstor_type = T.ty_arrow c.Stmt.copy_of c.Stmt.copy_to
    }
  in
  let data_ =
    { Stmt.
      ty_id = c.Stmt.copy_id;
      ty_vars = [];
      ty_type = T.ty_type;
      ty_cstors = ID.Map.singleton c.Stmt.copy_abstract cstor
    }
  in
  let decl_data = Stmt.data ~info [data_] in
  (* the definition of [c.copy_concrete], as pattern matching:
     [forall x:concrete. concr (abs x) = x] *)
  let decl_concr =
    let x = Var.make ~ty:c.Stmt.copy_of ~name:"x" in
    let lhs = T.app_const c.Stmt.copy_abstract [T.var x] in
    let rhs = T.var x in
    let def =
      { Stmt.
        rec_defined =
          Stmt.mk_defined ~attrs:[] c.Stmt.copy_concrete c.Stmt.copy_concrete_ty;
        rec_ty_vars=[];
        rec_eqns=Stmt.Eqn_nested [[x], [lhs], rhs, []];
      }
    in
    Stmt.axiom_rec ~info:Stmt.info_default [def]
  in
  (* return all new decls *)
  [decl_data; decl_concr]

let approx_threshold_ = 4 (* FUDGE *)

(* do we have an exact cardinal for [c.Stmt.copy_of], that is
   also small enough? *)
let has_small_exact_card card_concrete = match card_concrete with
  | Cardinality.Infinite
  | Cardinality.Unknown
  | Cardinality.QuasiFiniteGEQ _ -> None
  | Cardinality.Exact n ->
    (* if [n >= threshold] we approximate *)
    if Cardinality.Z.(compare n (of_int approx_threshold_) <= 0)
    then Some (Cardinality.Z.to_int n |> CCOpt.get_exn)
    else None

let attrs_of_ty state (ty:ty): Stmt.decl_attr list =
  (if AT.is_abstract state.env ty
   then [Stmt.Attr_abstract] else [])
  @
    (if AT.is_incomplete state.env ty
     then [Stmt.Attr_incomplete] else [])

(* [c] is a subset copy type with predicate [pred]; encode it as a new
   uninterpreted type [c], where [abstract] and [concrete] are regular functions
   with some axioms, and [pred] is valid all over [concrete c] *)
let copy_subset_as_uninterpreted_ty state ~info ~(pred:term) c : (_, _) Stmt.t list =
  let card_concrete =
    AT.cardinality_ty ~cache:state.at_cache state.env c.Stmt.copy_of
  in
  let card_abstract_upper_bound = has_small_exact_card card_concrete in
  let incomplete = card_abstract_upper_bound = None in
  let id_c = c.Stmt.copy_id in
  let ty_c = T.ty_const id_c in
  ID.Tbl.add state.copy_as_uninterpreted id_c ();
  Utils.debugf ~section 3 "@[copy type %a:@ should_be_incomplete=%B@]"
    (fun k -> k ID.pp id_c incomplete);
  (* be sure to register approximated types *)
  if incomplete then (
    TyTbl.add state.incomplete_types ty_c ();
  );
  (* declare the new (uninterpreted) type and functions *)
  let decl_c =
    let new_attr =
      if incomplete then Stmt.Attr_incomplete
      else match card_abstract_upper_bound with
        | None -> assert false
        | Some n ->
          (* must be an exact cardinal, but for the subtype it's only
             an upper bound *)
          Stmt.Attr_card_max_hint n
    in
    let old_attrs = attrs_of_ty state c.Stmt.copy_of in
    let attrs = new_attr :: old_attrs in
    Stmt.decl ~info ~attrs id_c c.Stmt.copy_ty
  and decl_abs =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_abstract c.Stmt.copy_abstract_ty
  and decl_conc =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_concrete c.Stmt.copy_concrete_ty
  in
  (* axiom [forall a:abs. abstract (concrete a) = a] *)
  let ax_abs_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    T.forall a
      (T.eq
         (T.var a)
         (T.app_const c.Stmt.copy_abstract
            [T.app_const c.Stmt.copy_concrete [T.var a]]))
    |> Stmt.axiom1 ~info
  (* axiom [forall a: abs. pred (concrete a)] *)
  and ax_pred_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    T.forall a
      (T.Red.app_whnf pred
         [T.app_const c.Stmt.copy_concrete [T.var a]])
    |> Stmt.axiom1 ~info
  (* if complete (concrete type is finite and small enough),
     axiom [forall c:conc. pred c => c = concrete (abstract c)] *)
  and ax_defined =
    if incomplete then []
    else (
      let co = Var.make ~ty:c.Stmt.copy_of ~name:"c" in
      let ax =
        T.forall co
          (T.imply
             (T.Red.app_whnf pred [T.var co])
             (T.eq
                (T.var co)
                (T.app_const c.Stmt.copy_concrete
                   [T.app_const c.Stmt.copy_abstract [T.var co]])))
        |> Stmt.axiom1 ~info
      in
      [ax]
    )
  in
  [decl_c; decl_abs; decl_conc; ax_abs_conc; ax_pred_conc]
  @ ax_defined

(* [c] is a quotient copy type with relation [rel]; encode it as a new
   uninterpreted type [c], where [abstract] and [concrete] are regular functions
   with some axioms, and [pred] is valid all over [concrete c] *)
let copy_quotient_as_uninterpreted_ty state ~info ~tty ~(rel:term) c : (_, _) Stmt.t list =
  let card_concrete =
    AT.cardinality_ty ~cache:state.at_cache state.env c.Stmt.copy_of
  in
  let card_abstract_upper_bound = has_small_exact_card card_concrete in
  let incomplete = card_abstract_upper_bound = None in
  let id_c = c.Stmt.copy_id in
  let ty_c = T.ty_const id_c in
  ID.Tbl.add state.copy_as_uninterpreted id_c ();
  Utils.debugf ~section 3 "@[copy type %a:@ should_be_incomplete=%B@]"
    (fun k -> k ID.pp id_c incomplete);
  if incomplete then (
    TyTbl.add state.incomplete_types ty_c ();
  );
  TyTbl.add state.abstract_types ty_c ();
  (* declare the new (uninterpreted) type and functions *)
  let decl_c =
    let incomp_attr =
      if incomplete then [Stmt.Attr_incomplete]
      else match card_abstract_upper_bound with
        | None -> assert false
        | Some n ->
          (* must be an exact cardinal, but for the copy it's only an upper bound *)
          [Stmt.Attr_card_max_hint n]
    in
    let old_attrs = attrs_of_ty state c.Stmt.copy_of in
    let attrs = Stmt.Attr_abstract :: incomp_attr @ old_attrs in
    Stmt.decl ~info ~attrs id_c c.Stmt.copy_ty
  and decl_abs =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_abstract c.Stmt.copy_abstract_ty
  and decl_conc =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_concrete c.Stmt.copy_concrete_ty
  in
  (* axiom [forall a:abs. abstract (concrete a) = a] *)
  let ax_abs_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    T.forall a
      (T.eq
         (T.var a)
         (T.app_const c.Stmt.copy_abstract
            [T.app_const c.Stmt.copy_concrete [T.var a]]))
    |> Stmt.axiom1 ~info
  (* axiom [forall a: abs. rel (concrete a) (concrete a)] *)
  and ax_rel_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    let conc_a = T.app_const c.Stmt.copy_concrete [T.var a] in
    T.forall a (T.Red.app_whnf rel [conc_a; conc_a])
    |> Stmt.axiom1 ~info
  (* axiom [forall a b: abs. rel (concrete a) (concrete b) => a = b] *)
  and ax_partition =
    let a = Var.make ~ty:ty_c ~name:"a" in
    let b = Var.make ~ty:ty_c ~name:"b" in
    let conc_a = T.app_const c.Stmt.copy_concrete [T.var a] in
    let conc_b = T.app_const c.Stmt.copy_concrete [T.var b] in
    T.forall_l [a; b]
      (T.imply
         (T.Red.app_whnf rel [conc_a; conc_b])
         (T.eq (T.var a) (T.var b)))
    |> Stmt.axiom1 ~info
  (* if complete (concrete type is finite and small enough),
     axiom [forall c:conc. (rel c c =>)? rel c (concrete (abstract c))] *)
  and ax_defined =
    if incomplete then []
    else (
      let co = Var.make ~ty:c.Stmt.copy_of ~name:"c" in
      let add_guard t = match tty with
        | `Partial -> T.imply (T.Red.app_whnf rel [T.var co; T.var co]) t
        | `Total -> t
      in
      let ax =
        T.forall co
          (add_guard
             (T.Red.app_whnf rel
                [T.var co;
                 T.app_const c.Stmt.copy_concrete
                   [T.app_const c.Stmt.copy_abstract [T.var co]]]))
        |> Stmt.axiom1 ~info
      in
      [ax]
    )
  in
  [decl_c; decl_abs; decl_conc; ax_abs_conc; ax_rel_conc; ax_partition]
  @ ax_defined

let is_incomplete_type_ state ty = TyTbl.mem state.incomplete_types ty
let is_abstract_type_ state ty = TyTbl.mem state.abstract_types ty

(* encode terms, perform the required approximations *)
let encode_term state pol t =
  let rec aux pol t = match T.repr t with
    | TI.Bind ((Binder.Forall | Binder.Exists) as q, v, _)
      when is_incomplete_type_ state (Var.ty v) ->
      (* might approximate this quantifier *)
      begin match T.approx_infinite_quant_pol_binder q pol with
        | `Keep -> aux' pol t
        | `Unsat_means_unknown res ->
          (* drop quantifier *)
          state.unsat_means_unknown <- true;
          res
      end
    | _ ->
      aux' pol t
  and aux' pol t =
    T.map_pol () pol t
      ~bind:(fun () v -> (), v)
      ~f:(fun () -> aux)
  in
  aux pol t

let elim pb =
  let env = Problem.env pb in
  let state = create_state ~env in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(fun stmt ->
        let info = Stmt.info stmt in
        match Stmt.view stmt with
          | Stmt.Copy c ->
            begin match c.Stmt.copy_wrt with
              | Stmt.Wrt_nothing -> copy_as_data ~info c
              | Stmt.Wrt_subset p ->
                copy_subset_as_uninterpreted_ty state ~info ~pred:p c
              | Stmt.Wrt_quotient (tty, r) ->
                copy_quotient_as_uninterpreted_ty state ~info ~tty ~rel:r c
            end
          | _ ->
            let stmt' =
              Stmt.map stmt ~ty:CCFun.id ~term:(encode_term state Pol.Pos)
            in
            [stmt']
      )
  in
  let pb' = Problem.add_unsat_means_unknown state.unsat_means_unknown pb' in
  pb', state

(** {2 Decoding} *)

module M = Model
module DT_util = M.DT_util

(* find, in the model, the concretization functions of copy types
   that were translated to uninterpreted types.

   Say [a := copy r] became uninterpreted and, in the model,
   [a := {a0, a1}]. Then we find the value of [r_of_a] (concretization fun),
   and build the map
   [a0 -> a_of_r (eval (r_of_a a0)); a1 -> a_of_r (eval (r_of_a a1))]
*)
let decode_concrete_ st m : term ID.Map.t =
  (* map [copy_id -> model of copy_concretize] *)
  let concrete_funs : ((_,_) Stmt.copy * (_,_) M.DT.t) ID.Map.t  =
    M.fold ID.Map.empty m
      ~values:(fun map (t,dt,_) -> match T.repr t with
        | TI.Const id ->
          begin match Env.find ~env:st.env id with
            | Some {Env.def=Env.Copy_concrete c; _}
              when ID.Tbl.mem st.copy_as_uninterpreted c.Stmt.copy_id ->
              assert (not (ID.Map.mem c.Stmt.copy_id map));
              ID.Map.add c.Stmt.copy_id (c, dt) map
            | _ -> map
          end
        | _ -> map
      )
  in
  M.fold ID.Map.empty m
    ~finite_types:(fun map (t,dom) -> match T.repr t with
      | TI.Const id when ID.Tbl.mem st.copy_as_uninterpreted id ->
        (* copy type as finite! *)
        let c, dt =
          try ID.Map.find id concrete_funs
          with Not_found ->
            errorf "could not find concretize function for %a in model" ID.pp id
        in
        List.fold_left
          (fun map dom_id ->
             let r = DT_util.apply dt (T.const dom_id) |> DT_util.to_term in
             let a = T.app_const c.Stmt.copy_abstract [r] in
             ID.Map.add dom_id a map)
          map dom
      | _ -> map
    )

(* decode a term, substituting the IDs in [map] *)
let decode_term (map:term ID.Map.t) (t:term): term =
  let rec aux t = match T.repr t with
    | TI.Const id ->
      begin match ID.Map.get id map with
        | None -> t
        | Some t' -> t'
      end
    | TI.App (f, l) ->
      let f = aux f in
      let l = List.map aux l in
      T.Red.app_whnf f l
    | _ -> aux' t
  and aux' t =
    T.map () t ~f:(fun () -> aux) ~bind:(fun () v->(), v)
  in
  aux t

let decode_model (st:decode_state) m : (_,_) Model.t =
  let env = st.env in
  let map = decode_concrete_ st m in
  Utils.debugf ~section 3
    "@[<2>decode model with map@ @[<hv>%a@]@]"
    (fun k->k (Utils.pp_seq CCFormat.(pair ~sep:(return "@ -> ") ID.pp T.pp))
        (ID.Map.to_iter map));
  let tr_term = decode_term map in
  Model.filter_map m
    ~finite_types:(fun (ty,dom) -> match T.repr ty with
      | TI.Const id when ID.Tbl.mem st.copy_as_uninterpreted id ->
        None (* drop copy types from model *)
      | _ -> Some (ty,dom))
    ~values:(fun (t,dt,k) -> match T.repr t with
      | TI.Const id ->
        begin match Env.find ~env id with
          | Some {Env.def=(Env.Copy_concrete _ | Env.Copy_abstract _); _} ->
            None (* drop `concrete` and `abstract` functions *)
          | _ ->
            let t = tr_term t in
            let dt = M.DT.map ~ty:CCFun.id ~term:tr_term dt in
            Some (t,dt,k)
        end
      | _ ->
        let t = tr_term t in
        let dt = M.DT.map ~ty:CCFun.id ~term:tr_term dt in
        Some (t,dt,k)
    )

(** {2 Pipe} *)

let pipe ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.P in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  let decode st = Problem.Res.map_m ~f:(decode_model st) in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono; Copy, Present])
    ~map_spec:Transform.Features.(update_l [Copy, Absent; Data, Present; Fun, Eqn_nested])
    ~on_encoded
    ~encode:elim
    ~decode
    ()
