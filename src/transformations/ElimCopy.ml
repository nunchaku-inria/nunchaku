
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module Pol = Polarity
module AT = AnalyzeType.Make(T)
module Red = Reduce.Make(T)
module TyTbl = U.Tbl

let name = "elim_copy"
let section = Utils.Section.make name

type term = T.t
type ty = T.t

type state = {
  env: (term, ty) Env.t;
  approximate_types: unit TyTbl.t; (* copy types that are approximate *)
  copy_as_uninterpreted: unit ID.Tbl.t; (* copy types mapped to uninterpreted types *)
  at_cache: AT.cache;
  mutable unsat_means_unknown: bool;
}

type decode_state = state

let create_state ~env = {
  env;
  at_cache=AT.create_cache ();
  approximate_types=TyTbl.create 16;
  copy_as_uninterpreted=ID.Tbl.create 16;
  unsat_means_unknown=false;
}

let error msg = failwith ("in " ^ name ^ ": " ^ msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

(** {2 Encoding} *)

(* encode the copy type as a datatype *)
let copy_as_data ~info (c:_ Stmt.copy): _ Stmt.t list =
  (* the datatype itself, whose cstor is [c.copy_abstract] *)
  let cstor =
    { Stmt.
      cstor_name = c.Stmt.copy_abstract;
      cstor_args = [c.Stmt.copy_of];
      cstor_type = U.ty_arrow c.Stmt.copy_of c.Stmt.copy_to
    }
  in
  let data_ =
    { Stmt.
      ty_id = c.Stmt.copy_id;
      ty_vars = [];
      ty_type = U.ty_type;
      ty_cstors = ID.Map.singleton c.Stmt.copy_abstract cstor
    }
  in
  let decl_data = Stmt.data ~info [data_] in
  (* the definition of [c.copy_concrete], as pattern matching:
     [forall x:concrete. concr (abs x) = x] *)
  let decl_concr =
    let x = Var.make ~ty:c.Stmt.copy_of ~name:"x" in
    let lhs = U.app_const c.Stmt.copy_abstract [U.var x] in
    let rhs = U.var x in
    let def =
      { Stmt.
        rec_defined = Stmt.mk_defined c.Stmt.copy_concrete c.Stmt.copy_concrete_ty;
        rec_vars=[];
        rec_eqns=Stmt.Eqn_nested [[x], [lhs], rhs, []];
      }
    in
    Stmt.axiom_rec ~info:Stmt.info_default [def]
  in
  (* return all new decls *)
  [decl_data; decl_concr]

let approx_threshold_ = 30 (* FUDGE *)

(* [c] is a copy type with predicate [pred]; encode it as a new uninterpreted
   type [c], where [abstract] and [concrete] are regular functions with
   some axioms, and [pred] is valid all over [concrete c] *)
let copy_as_finite_ty state ~info ~(pred:term) c : _ Stmt.t list =
  let card_concrete =
    AT.cardinality_ty ~cache:state.at_cache state.env c.Stmt.copy_of
  in
  (* should we do an approximation of [c.Stmt.copy_of]? *)
  let should_approx = match card_concrete with
    | Cardinality.Infinite
    | Cardinality.Unknown -> true
    | Cardinality.Exact n
    | Cardinality.QuasiFiniteGEQ n ->
      (* if [n >= threshold] we approximate *)
      Cardinality.Z.(compare (of_int approx_threshold_) n <= 0)
  in
  let id_c = c.Stmt.copy_id in
  let ty_c = U.ty_const id_c in
  ID.Tbl.add state.copy_as_uninterpreted id_c ();
  Utils.debugf ~section 3 "@[copy type %a:@ should_approx=%B@]"
    (fun k->k ID.print id_c should_approx);
  (* be sure to register approximated types *)
  if should_approx
  then TyTbl.add state.approximate_types ty_c ();
  (* declare the new (uninterpreted) type and functions *)
  let decl_c =
    let attrs =
      if should_approx then [] else [Stmt.Attr_card_hint card_concrete]
    in
    Stmt.decl ~info ~attrs id_c c.Stmt.copy_ty
  and decl_abs =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_abstract c.Stmt.copy_abstract_ty
  and decl_conc =
    Stmt.decl ~info ~attrs:[] c.Stmt.copy_concrete c.Stmt.copy_concrete_ty
  in
  (* axiom [forall a:abs. abstract (concrete a) = a] *)
  let ax_abs_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    U.forall a
      (U.eq
         (U.var a)
         (U.app_const c.Stmt.copy_abstract
            [U.app_const c.Stmt.copy_concrete [U.var a]]))
    |> Stmt.axiom1 ~info
  (* axiom [forall a: abs. pred (concrete a)] *)
  and ax_pred_conc =
    let a = Var.make ~ty:ty_c ~name:"a" in
    U.forall a
      (Red.app_whnf pred
         [U.app_const c.Stmt.copy_concrete [U.var a]])
    |> Stmt.axiom1 ~info
  (* if no approximation (concrete type is finite and small enough),
     axiom [forall r:repr. pred r => r = concrete (abstract r)] *)
  and ax_defined =
    if should_approx then []
    else (
      let r = Var.make ~ty:c.Stmt.copy_of ~name:"r" in
      let ax =
        U.forall r
          (U.imply
             (Red.app_whnf pred [U.var r])
             (U.eq
                (U.var r)
                (U.app_const c.Stmt.copy_concrete
                   [U.app_const c.Stmt.copy_abstract [U.var r]])))
        |> Stmt.axiom1 ~info
      in
      [ax]
    )
  in
  [decl_c; decl_abs; decl_conc; ax_abs_conc; ax_pred_conc]
    @ ax_defined

let is_approx_type_ state ty = TyTbl.mem state.approximate_types ty

(* encode terms, perform the required approximations *)
let encode_term state pol t =
  let rec aux pol t = match T.repr t with
    | TI.Bind ((`Forall | `Exists) as q, v, _)
      when is_approx_type_ state (Var.ty v) ->
      (* might approximate this quantifier *)
      begin match U.approx_infinite_quant_pol q pol with
        | `Keep -> aux' pol t
        | `Unsat_means_unknown res ->
          (* drop quantifier *)
          state.unsat_means_unknown <- true;
          res
      end
    | _ ->
      aux' pol t
  and aux' pol t =
    U.map_pol () pol t
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
            begin match c.Stmt.copy_pred with
              | None -> copy_as_data ~info c
              | Some p -> copy_as_finite_ty state ~info ~pred:p c
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
  let concrete_funs : (_ Stmt.copy * _ M.DT.t) ID.Map.t  =
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
            errorf "could not find concretize function for %a in model" ID.print id
        in
        List.fold_left
          (fun map dom_id ->
             let r = DT_util.apply dt (U.const dom_id) |> DT_util.to_term in
             let a = U.app_const c.Stmt.copy_abstract [r] in
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
      Red.app_whnf f l
    | _ -> aux' t
  and aux' t =
    U.map () t ~f:(fun () -> aux) ~bind:(fun () v->(), v)
  in
  aux t

let decode_model (st:decode_state) m : _ Model.t =
  let env = st.env in
  let map = decode_concrete_ st m in
  Utils.debugf ~section 3
    "@[<2>decode model with map@ @[<hv>%a@]@]"
    (fun k->k (ID.Map.print ID.print P.print) map);
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
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.print)
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
