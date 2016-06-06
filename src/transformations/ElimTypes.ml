
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Simple Types} *)

open Nunchaku_core

module TI = TermInner
module TyI = TypeMono
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module Ty = TypeMono.Make(T)
module PStmt = Stmt.Print(P)(P)
module M = Model

let name = "elim_types"
let section = Utils.Section.make name

type inv = <eqn:[`Absent]; ty:[`Mono]; ind_preds:[`Absent]>

type error = string
exception Error of error
let () = Printexc.register_printer
    (function (Error e) -> Some (Utils.err_sprintf "in elim_types: %s" e)
            | _ -> None)

let error_ e = raise (Error e)
let errorf_ msg = Utils.exn_ksprintf msg ~f:error_

(** {2 Encoding} *)

type state = {
  mutable ty_to_pred: ID.t Ty.Map.t;
    (* type -> predicate for this type *)
  mutable pred_to_ty: T.t ID.Map.t;
    (* predicate -> type it encodes *)
  parametrized_ty: unit ID.Tbl.t;
    (* parametrized ty *)
  sigma: T.t Signature.t;
    (* signature, for decoding purpose *)
}

let create_state ~sigma () = {
  ty_to_pred=Ty.Map.empty;
  pred_to_ty=ID.Map.empty;
  parametrized_ty=ID.Tbl.create 16;
  sigma;
}

(* find predicate for this type
   precondition: [t] a type for which we created a new predicate *)
let find_pred state t =
  assert (Ty.is_ty t);
  Ty.Map.find t state.ty_to_pred

let encode_var subst v =
  let v' = Var.fresh_copy v |> Var.set_ty ~ty:U.ty_unitype in
  let subst = Var.Subst.add ~subst v v' in
  subst, v'

let rec encode_term state subst t = match T.repr t with
  | TI.Var v -> U.var (Var.Subst.find_exn ~subst v)
  | TI.Bind ((`Forall | `Exists) as b, v, body) ->
    let p = find_pred state (Var.ty v) in
    let subst, v' = encode_var subst v in
    (* add guard, just under the quantifier. *)
    begin match b with
      | `Forall ->
        (* [forall v:t. F] -> [forall v. is_t v => F] *)
        U.forall v'
          (U.imply
             (U.app_const p [U.var v'])
             (encode_term state subst body))
      | `Exists ->
        (* [exists v:t. F] -> [exists v. is_t v & F] *)
        U.exists v'
          (U.and_
             [ U.app_const p [U.var v']
             ; encode_term state subst body ])
    end
  | TI.Bind (`Fun, _, _) -> Utils.not_implemented "elim_types for λ"
  | TI.Bind (`TyForall, _, _) -> assert false
  | _ ->
    U.map subst t ~f:(encode_term state) ~bind:encode_var

(* types are all sent to [state.dummy_ty] *)
let encode_ty state _ t =
  assert (Ty.is_ty t);
  assert (Ty.Map.mem t state.ty_to_pred);
  U.ty_unitype

(* mangle the type into a valid identifier *)
let rec mangle_ty_ out t = match Ty.repr t with
  | TyI.Builtin b -> CCFormat.string out (TyI.Builtin.to_string b)
  | TyI.Arrow _ -> assert false
  | TyI.Const id -> ID.print_name out id
  | TyI.App (_,[]) -> assert false
  | TyI.App (a,l) ->
    Format.fprintf out "%a_%a"
      mangle_ty_ a (CCFormat.list ~start:"" ~stop:"" ~sep:"_" mangle_ty_) l

(* add binding [ty -> pred] *)
let add_pred_ state ty pred =
  state.ty_to_pred <- Ty.Map.add ty pred state.ty_to_pred;
  state.pred_to_ty <- ID.Map.add pred ty state.pred_to_ty;
  Utils.debugf ~section 3 "@[<2>map type `@[%a@]`@ to predicate `%a`@]"
    (fun k->k P.print ty ID.print pred);
  ()

let as_id_ ty = match T.repr ty with
  | TI.Const id -> Some id
  | _ -> None

(* ensure the type maps to some predicate, and return it
  @return Some p where p is the predicate for this type, or None if ty=unitype *)
let map_to_predicate state ty =
  try Some (Ty.Map.find ty state.ty_to_pred)
  with Not_found ->
    begin match Ty.repr ty with
      | TyI.Const id ->
        errorf_ "atomic type `%a` should have been mapped to a predicate" ID.print id
      | TyI.Arrow _ -> assert false
      | TyI.Builtin `Unitype ->
        None (* no need to declare *)
      | TyI.Builtin `Type
      | TyI.Builtin `Kind -> assert false
      | TyI.Builtin `Prop ->
        error_ "cannot make a predicate for `prop`"
      | TyI.App (f, l) ->
        match as_id_ f with
        | None -> errorf_ "expected constructor type, got `@[%a@]`" P.print ty
        | Some id ->
          let n = List.length l in
          if not (ID.Tbl.mem state.parametrized_ty id)
          then errorf_ "type constructor `%a`/%d has not been declared" ID.print id n;
          (* find name *)
          let name = ID.make_f "is_%a" mangle_ty_ ty in
          add_pred_ state ty name;
          Some name
    end

let ensure_maps_to_predicate state ty =
  ignore (map_to_predicate state ty)

let encode_stmt state st =
  Utils.debugf ~section 3 "@[<2>encode statement@ `@[%a@]`@]"
    (fun k->k PStmt.print st);
  let info = Stmt.info st in
  match Stmt.view st with
  | Stmt.Decl (id, ty, attrs) when U.ty_returns_Type ty ->
    (* type declaration *)
    let _, args, _ = U.ty_unfold ty in
    assert (List.for_all U.ty_is_Type args);
    begin match args with
      | [] ->
        (* TODO: combine the min/max of cardinalities for unitype,
           OR emit some constraint on the predicate *)
        List.iter
          (function
            | Stmt.Attr_card_max _
            | Stmt.Attr_card_min _ ->
              errorf_ "cannot encode cardinality bounds of %a to TPTP" ID.print id
            | _ -> ())
          attrs;
        (* atomic type, easy *)
        let p = ID.make_f "is_%a" ID.print_name id in
        add_pred_ state (U.const id) p
      | _::_ ->
        (* not atomic, we need to declare each instance later *)
        ID.Tbl.add state.parametrized_ty id ();
    end;
    [] (* remove statement *)
  | Stmt.Decl (id, ty, attrs) when U.ty_returns_Prop ty ->
    (* symbol declaration *)
    let _, args, _ = U.ty_unfold ty in
    List.iter (ensure_maps_to_predicate state) args;
    (* new type [term -> term -> ... -> term -> prop] *)
    let ty' =
      U.ty_arrow_l
        (List.map (fun _ -> U.ty_unitype) args)
        U.ty_prop
    in
    [ Stmt.decl ~info ~attrs id ty' ]
  | Stmt.Decl (id, ty, attrs) ->
    let _, args, ret = U.ty_unfold ty in
    (* declare every argument type, + the return type *)
    let pred_ret = map_to_predicate state ret in
    let preds = List.map (map_to_predicate state) args in
    (* new type [term -> term -> ... -> term -> term] *)
    let ty' =
      U.ty_arrow_l
        (List.map (fun _ -> U.ty_unitype) args)
        U.ty_unitype
    in
    (* typing clause:
      is_ty1(x1) & ... & is_tyn(xn) => is_ty(id(x1...xn)) *)
    let ty_clause = match pred_ret with
    | None -> U.true_
    | Some p_ret ->
      let vars = List.mapi (fun i _ -> Var.makef ~ty:U.ty_unitype "v_%d" i) args in
      U.forall_l vars
        (U.imply_l
           (List.map2
              (fun pred v -> match pred with
                 | None -> U.true_
                 | Some p -> U.app_const p [U.var v])
              preds vars)
           (U.app_const p_ret [U.app_const id (List.map U.var vars)]))
    in
    [ Stmt.decl ~info ~attrs id ty'; Stmt.axiom1 ~info ty_clause ]
  | _ ->
    [Stmt.map_bind Var.Subst.empty st
      ~term:(encode_term state)
      ~ty:(encode_ty state)
      ~bind:Var.Subst.rename_var]

let transform_pb pb =
  let sigma = Problem.signature pb in
  let state = create_state ~sigma () in
  let pb' = Problem.flat_map_statements pb ~f:(encode_stmt state) in
  pb', state

(** {2 Decoding} *)

module DTU = M.DT_util(T)

type retyping = {
  rety_domains: ID.t list Ty.Map.t; (* type -> domain *)
  rety_map: ID.t ID.Map.t Ty.Map.t; (* type -> (uni_const -> const) *)
}

(* for each type predicate, find cardinality and build a new set of
   constants for this type *)
let rebuild_types state m : retyping =
  (* set of constants for unitype *)
  let uni_domain =
    CCList.find_map
      (fun (ty,l) -> if U.equal ty U.ty_unitype then Some l else None)
      m.M.finite_types
    |> (function
      | Some x -> x
      | None -> error_ "could not find `unitype` in model")
  in
  M.fold
    {rety_domains=Ty.Map.empty; rety_map=Ty.Map.empty}
    m
    ~constants:(fun rety _ -> rety)
    ~finite_types:(fun rety _ -> rety)
    ~funs:(fun rety (t,vars,dt,_) -> match vars, T.repr t with
      | [v], TI.Const pred_id when ID.Map.mem pred_id state.pred_to_ty ->
        (* (unary) type predicate: evaluate it on [uni_domain] to find
           the actual subset, then make new constants *)
        let ty = ID.Map.find pred_id state.pred_to_ty in
        let uni_domain_sub =
          CCList.filter_map
            (fun id ->
               let subst = Var.Subst.add ~subst:Var.Subst.empty v (U.const id) in
               let image = DTU.eval ~subst dt in
               match T.repr image with
                 | TI.Builtin `True ->
                   (* belongs to domain! *)
                   Some id
                 | TI.Builtin `False
                 | TI.Builtin (`Undefined _) -> None
                 | _ -> errorf_ "unexpected value for %a on %a" ID.print pred_id ID.print id
            )
            uni_domain
        in
        let map =
          List.mapi
            (fun i c -> c, ID.make_f "%a_%d" mangle_ty_ ty i)
            uni_domain_sub
          |> ID.Map.of_list
        in
        let dom = ID.Map.values map |> Sequence.to_list in
        Utils.debugf ~section 3
          "@[<2>domain of type `%a`@ is {@[%a@]},@ map to @[[%a]@]@]"
          (fun k->k P.print ty (CCFormat.list ID.print) dom
              (ID.Map.print ID.print ID.print) map);
        { rety_domains = Ty.Map.add ty dom rety.rety_domains;
          rety_map = Ty.Map.add ty map rety.rety_map
        }
      | _ -> rety)

let ty_of_id_ state id =
  match Signature.find ~sigma:state.sigma id with
    | Some t -> t
    | None -> errorf_ "could not find the type of `@[%a@]`" ID.print id

(* what should be the type of [t]? We assume [t] is not a constant
   from the domain of [unitype] *)
let rec expected_ty state t = match T.repr t with
  | TI.Const id -> ty_of_id_ state id
  | TI.App (f, _) ->
    let _, _, ret = expected_ty state f |> U.ty_unfold in
    ret
  | _ -> errorf_ "could not find the expected type of `@[%a@]`" P.print t

(* decode an atomic term t: recursively infer the expected types,
   and use the corresponding constants from [rety] *)
let decode_term ?(subst=Var.Subst.empty) state rety t ty =
  (* we expect [t:ty] *)
  let rec aux t ty = match T.repr t with
    | TI.Var v ->
      begin match Var.Subst.find ~subst v with
        | Some v' -> U.var v'
        | None ->
          errorf_ "variable `%a` not bound in `@[%a@]`"
            Var.print_full v (Var.Subst.print Var.print_full) subst
      end
    | TI.App (f, l) ->
      (* use the expected type of [f] *)
      let _, ty_args, ty_ret = expected_ty state f |> U.ty_unfold in
      assert (U.equal ty_ret ty); (* expected type must match *)
      assert (List.length ty_args = List.length l);
      assert (U.is_const f);
      let l = List.map2 aux l ty_args in
      U.app f l
    | TI.Const id ->
      begin match Ty.Map.get ty rety.rety_map with
        | None -> t
        | Some map ->
          (* if [id] is a unitype domain constant, replace it *)
          ID.Map.get id map
          |> CCOpt.maybe U.const t
      end
    | _ ->
      U.map () t
        ~f:(fun () t ->
          let ty = expected_ty state t in
          aux t ty)
        ~bind:(fun _ _ -> assert false)
  in
  aux t ty

(* transform unityped variables into typed variables *)
let decode_vars ?(subst=Var.Subst.empty) ty vars =
  let _, args, _ = U.ty_unfold ty in
  assert (List.length args = List.length vars);
  (* map each variable to the corresponding type *)
  Utils.fold_map
    (fun subst (v,ty) ->
       let v' = Var.set_ty v ~ty in
       Var.Subst.add ~subst v v', v')
    subst (List.combine vars args)

let decode_model ~state m =
  let rety = rebuild_types state m in
  let dec_t ?subst t ty = decode_term state rety ?subst t ty in
  let m =
    M.filter_map m
      ~constants:(fun (t,u,k) ->
        let ty = expected_ty state t in
        Some (dec_t t ty, dec_t u ty, k))
      ~finite_types:(fun (t,_) ->
        (* only one possible choice: unitype, and we remove it *)
        assert (U.equal t U.ty_unitype);
        None)
      ~funs:(fun (t,vars,dt,k) -> match T.repr t with
        | TI.Const p_id when ID.Map.mem p_id state.pred_to_ty ->
          None (* remove typing predicates from model *)
        | _ ->
          Utils.debugf ~section 5
            "@[<2>decode @[%a %a@]@ := `@[%a@]@]"
            (fun k->k P.print t (CCFormat.list Var.print) vars
                (M.DT.print P.print') dt);
          let ty = expected_ty state t in
          let ty_ret = U.ty_returns ty in
          let subst, vars = decode_vars ty vars in
          let dt' =
            M.DT.test
              (List.map
                 (fun (tests,then_) ->
                    let tests' =
                      List.map
                        (fun (v,t) ->
                           let v' = Var.Subst.find_exn ~subst v in
                           let ty_v = Var.ty v' in
                           v', dec_t ~subst t ty_v)
                        tests
                    in
                    let then_' = dec_t ~subst then_ ty_ret in
                    tests', then_')
                 dt.M.DT.tests)
              ~else_:(dec_t ~subst dt.M.DT.else_ ty_ret)
          in
          let t' = dec_t t ty in
          Some (t', vars, dt', k)
      )
  in
  (* add new types' domains *)
  Ty.Map.to_seq rety.rety_domains
    |> Sequence.fold
      (fun m (ty,dom) -> M.add_finite_type m ty dom)
      m

(** {2 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check:_ =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name Ppb.print)
  in
  Transform.make
    ~name
    ?on_decoded
    ~on_encoded
    ~encode:transform_pb
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
         name (Problem.Res.print P.print' P.print)]
    else []
  in
  pipe_with ~check ~print ~on_decoded
    ~decode:(fun state -> Problem.Res.map_m ~f:(decode_model ~state))
