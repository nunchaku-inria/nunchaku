
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
module DT = M.DT
module Subst = Var.Subst

type term = T.t

let name = "elim_types"
let section = Utils.Section.make name

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
  env: (T.t,T.t) Env.t;
  (* signature, for decoding purpose *)
  side_axioms: (T.t, T.t) Statement.t CCVector.vector;
  (* new declarations *)
}

let create_state ~env () = {
  ty_to_pred=Ty.Map.empty;
  pred_to_ty=ID.Map.empty;
  parametrized_ty=ID.Tbl.create 16;
  env;
  side_axioms=CCVector.create();
}

(* find predicate for this type
   precondition: [t] a type for which we created a new predicate *)
let find_pred state (t:T.t): ID.t =
  assert (Ty.is_ty t);
  try Ty.Map.find t state.ty_to_pred
  with Not_found ->
    errorf_ "could not find the predicate for type@ `@[%a@]`" P.print t

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
let rec encode_ty state ~top x t = match Ty.repr t with
  | TyI.Builtin `Prop ->
    if top then U.ty_prop
    else error_ "cannot encode type prop";
  | TyI.Arrow (a,b) ->
    U.ty_arrow
      (encode_ty state ~top:false x a)
      (encode_ty state ~top x b)
  | _ ->
    assert (Ty.is_ty t);
    assert (Ty.Map.mem t state.ty_to_pred);
    U.ty_unitype

(* mangle the type into a valid identifier *)
let mangle_ty_ = Ty.mangle ~sep:"_"

(* add binding [ty -> pred] *)
let add_pred_ state ty pred =
  state.ty_to_pred <- Ty.Map.add ty pred state.ty_to_pred;
  state.pred_to_ty <- ID.Map.add pred ty state.pred_to_ty;
  Utils.debugf ~section 3 "@[<2>map type `@[%a@]`@ to predicate `%a`@]"
    (fun k->k P.print ty ID.print pred);
  let ty_pred = U.ty_arrow U.ty_unitype U.ty_prop in
  (* declare the predicate *)
  let decl_pred =
    Stmt.decl ~info:Stmt.info_default ~attrs:[] pred ty_pred
  in
  (* witness that the type is inhabited.  *)
  let ax_inhabited =
    let v = Var.makef ~ty:U.ty_unitype "witness_%s" (mangle_ty_ ty) in
    U.exists v (U.app_const pred [U.var v])
    |> Stmt.axiom1 ~info:Stmt.info_default
  in
  CCVector.push state.side_axioms decl_pred;
  CCVector.push state.side_axioms ax_inhabited;
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
            let name = ID.make_f "@[<h>is_%s@]" (mangle_ty_ ty) in
            add_pred_ state ty name;
            Some name
    end

(* ensure  that the immediate arguments and return type map to predicates *)
let ensure_maps_to_predicate state ty =
  let aux ty = match Ty.repr ty with
    | TyI.Builtin `Prop -> ()
    | _ -> ignore (map_to_predicate state ty)
  in
  let _, args, ret = U.ty_unfold ty in
  List.iter aux args;
  aux ret;
  ()

(* type of pred [p] has at most [n] elements, return axiom
   [exists x1...xn. p x_i & forall y. p y => (y = x1 | .... | y = xn)] *)
let encode_max_card_ ~(pred:ID.t) n =
  let mk_pred = U.app_const pred in
  let xs =
    CCList.init n
      (fun i -> Var.makef ~ty:U.ty_unitype "x_%d" i)
  and y =
    Var.make ~name:"y" ~ty:U.ty_unitype
  in
  let guard_pred_x = U.and_ (List.map (fun x -> mk_pred [U.var x]) xs) in
  let form_y_belongs_xs =
    U.forall y
      (U.imply
         (mk_pred [U.var y])
         (U.or_
            (List.map (fun x -> U.eq (U.var x) (U.var y)) xs)))
  in
  let ax =
    U.exists_l xs
      (U.and_ [guard_pred_x; form_y_belongs_xs])
  in
  [Stmt.axiom1 ~info:Stmt.info_default ax]

(* the type of [pred] has at least [n] elements, return list of axiom
   [exists x1...xn. pred x_i & xi != xj] *)
let encode_min_card_ ~(pred:ID.t) n =
  let mk_pred = U.app_const pred in
  let xs =
    CCList.init n
      (fun i -> Var.makef ~ty:U.ty_unitype "x_%d" i)
  in
  let guard_pred_x = U.and_ (List.map (fun x -> mk_pred [U.var x]) xs) in
  let pairwise_distinct =
    CCList.diagonal xs
    |> List.map (fun (x1,x2) -> U.neq (U.var x1) (U.var x2))
  in
  let ax =
    U.exists_l xs
      (U.and_ (guard_pred_x :: pairwise_distinct))
  in
  [Stmt.axiom1 ~info:Stmt.info_default ax]

let encode_stmt_ state st : (_,_) Stmt.t list =
  let info = Stmt.info st in
  match Stmt.view st with
    | Stmt.Decl ({Stmt.defined_ty=ty; _} as d) when U.ty_returns_Type ty ->
      let id = Stmt.id_of_defined d in
      let attrs = Stmt.attrs_of_defined d in
      (* type declaration *)
      let _, args, _ = U.ty_unfold ty in
      assert (List.for_all U.ty_is_Type args);
      (* remove statement, but we might have some specific axioms
         related to cardinalities *)
      begin match args with
        | [] ->
          (* atomic type, easy *)
          let p = ID.make_f "is_%a" ID.print_name id in
          add_pred_ state (U.const id) p;
          (* emit some constraint on the predicate for cardinalities *)
          CCList.flat_map
            (function
              | Stmt.Attr_card_max i -> encode_max_card_ ~pred:p i
              | Stmt.Attr_card_min i -> encode_min_card_ ~pred:p i
              | _ -> [])
            attrs
        | _::_ ->
          (* not atomic, we need to declare each instance later *)
          ID.Tbl.add state.parametrized_ty id ();
          []
      end
    | Stmt.Decl ({Stmt.defined_ty=ty; _} as d) when U.ty_returns_Prop ty ->
      let id = Stmt.id_of_defined d in
      let attrs = Stmt.attrs_of_defined d in
      (* symbol declaration *)
      ensure_maps_to_predicate state ty;
      let _, args, _ = U.ty_unfold ty in
      (* new type [term -> term -> ... -> term -> prop] *)
      let ty' =
        U.ty_arrow_l
          (List.map (fun _ -> U.ty_unitype) args)
          U.ty_prop
      in
      [ Stmt.decl ~info ~attrs id ty' ]
    | Stmt.Decl d ->
      let id = Stmt.id_of_defined d in
      let attrs = Stmt.attrs_of_defined d in
      let ty = Stmt.ty_of_defined d in
      let _, args, ret = U.ty_unfold ty in
      assert (not (U.ty_is_Prop ret));
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
         ~term:(fun subst _ -> encode_term state subst)
         ~ty:(encode_ty state ~top:true)
         ~bind:Var.Subst.rename_var]

let encode_stmt state st =
  Utils.debugf ~section 3 "@[<2>encode statement@ `@[%a@]`@]"
    (fun k->k PStmt.print st);
  let st' = encode_stmt_ state st in
  let res =
    CCList.append
      (CCVector.to_list state.side_axioms)
      st'
  in
  CCVector.clear state.side_axioms;
  res

(* TODO: more accurate spec *)
let transform_pb pb =
  let env = Problem.env pb in
  let state = create_state ~env () in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(encode_stmt state)
  in
  pb', state

(** {2 Decoding} *)

type retyping = {
  rety_domains: ID.t list Ty.Map.t; (* type -> domain *)
  rety_map: ID.t ID.Map.t Ty.Map.t; (* type -> (uni_const -> const) *)
}

(* for each type predicate, find cardinality of the corresponding type,
   and build a new set of constants for this type *)
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
    ~finite_types:(fun rety _ -> rety)
    ~values:(fun rety (t,dt,_) -> match T.repr t with
      | TI.Const pred_id when ID.Map.mem pred_id state.pred_to_ty ->
        (* (unary) type predicate: evaluate it on [uni_domain] to find
           the actual subset, then make new constants *)
        assert (DT.num_vars dt >= 1);
        let ty = ID.Map.find pred_id state.pred_to_ty in
        let uni_domain_sub =
          CCList.filter_map
            (fun id ->
               let image =
                 M.DT_util.apply dt (U.const id) |> M.DT_util.to_term
               in
               match T.repr image with
                 | TI.Builtin `True ->
                   (* belongs to domain! *)
                   Some id
                 | TI.Builtin `False
                 | TI.Builtin (`Undefined_atom _) -> None
                 | _ -> errorf_ "unexpected value for %a on %a" ID.print pred_id ID.print id
            )
            uni_domain
        in
        let map =
          List.mapi
            (fun i c -> c, ID.make_f "$%s_%d" (mangle_ty_ ty) i)
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
  match Env.find_ty ~env:state.env id with
    | Some t -> t
    | None -> errorf_ "could not find the type of `@[%a@]`" ID.print id

(* what should be the type of [t]? We assume [t] is not a constant
   from the domain of [unitype] *)
let rec expected_ty state t = match T.repr t with
  | TI.Const id -> ty_of_id_ state id
  | TI.App (f, _) ->
    let _, _, ret = expected_ty state f |> U.ty_unfold in
    ret
  | TI.Builtin (`Undefined_atom (_,ty)) -> ty
  | _ -> errorf_ "could not find the expected type of `@[%a@]`" P.print t

let retype_find rety ty = Ty.Map.get ty rety.rety_map

let is_undefined_atom_ t = match T.repr t with
  | TI.Builtin (`Undefined_atom _) -> true
  | _ -> false

(* decode an atomic term [t]: recursively infer the expected types,
   and use the corresponding constants from [rety] *)
let decode_term ?(subst=Var.Subst.empty) state rety t ty =
  (* decode [t], expecting [t:ty] *)
  let rec aux t ty = match T.repr t with
    | TI.Var v ->
      begin match Var.Subst.find ~subst v with
        | Some v' -> U.var v'
        | None ->
          errorf_ "variable `%a` not bound in `@[%a@]`"
            Var.print_full v (Var.Subst.print Var.print_full) subst
      end
    | TI.App (f, l) when is_undefined_atom_ f ->
      (* must infer type of [f] using arguments: its expected type
         is [typeof l -> ty] *)
      let l, tys = List.map aux' l |> List.split in
      let f = aux f (U.ty_arrow_l tys ty) in
      U.app f l
    | TI.App (f, l) ->
      (* use the expected type of [f] *)
      let _, ty_args, ty_ret = expected_ty state f |> U.ty_unfold in
      assert (U.equal ty_ret ty); (* expected type must match *)
      assert (List.length ty_args = List.length l);
      assert (U.is_const f);
      let l = List.map2 aux l ty_args in
      U.app f l
    | TI.Builtin (`Undefined_atom (c,_ty')) ->
      U.builtin (`Undefined_atom (c,ty))
    | TI.Const id ->
      begin match retype_find rety ty with
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

  (* decode [t], not knowing its type; or fail if it can't be inferred *)
  and aux' t = match T.repr t with
    | TI.Var v ->
      begin match Var.Subst.find ~subst v with
        | Some v' -> U.var v', Var.ty v'
        | None ->
          errorf_ "variable `%a` not bound in `@[%a@]`"
            Var.print_full v (Var.Subst.print Var.print_full) subst
      end
    | TI.Const _ -> t, expected_ty state t
    | TI.App (f, _) ->
      (* use the expected type of [f],  then fallback on [aux] *)
      let _, _, ty_ret = expected_ty state f |> U.ty_unfold in
      aux t ty_ret, ty_ret
    | _ -> errorf_ "could not infer expected type of `@[%a@]`" P.print t
  in
  aux t ty

(* transform unityped variables of [dt] into typed variables *)
let decode_vars ty dt =
  let _, args, _ = U.ty_unfold ty in
  let vars = DT.vars dt in
  assert (List.length args = List.length vars);
  (* map each variable to the corresponding type *)
  let subst =
    List.fold_left2
      (fun subst v ty ->
         let v' = Var.set_ty v ~ty |> Var.fresh_copy in
         Subst.add ~subst v v')
      Subst.empty
      vars
      args
  in
  M.DT_util.map_vars ~subst dt

let decode_model ~state m =
  let rety = rebuild_types state m in
  let dec_t ?subst t ty = decode_term state rety ?subst t ty in
  let m =
    M.filter_map m
      ~finite_types:(fun (t,_) ->
        (* only one possible choice: unitype, and we remove it *)
        assert (U.equal t U.ty_unitype);
        None)
      ~values:(fun (t,dt,k) -> match T.repr t with
        | TI.Const p_id when ID.Map.mem p_id state.pred_to_ty ->
          None (* remove typing predicates from model *)
        | _ ->
          Utils.debugf ~section 5
            "@[<2>decode @[%a@]@ := `@[%a@]@]"
            (fun k->k P.print t (M.DT.print P.print' P.print) dt);
          let ty = expected_ty state t in
          let ty_ret = U.ty_returns ty in
          let dt = decode_vars ty dt in
          let dt' =
            DT.filter_map dt
              ~test:(fun v t ->
                let ty_v = Var.ty v in
                match T.repr t, retype_find rety ty_v with
                  | TI.Const id, Some map when not (ID.Map.mem id map) ->
                    (* [ty_v] is a finite type whose elements
                           have been encoded into [domain map].
                           Since [t] is a constant outside this
                           domain, the test is necessarily false
                           and must be removed *)
                    None
                  | _ ->
                    Some (dec_t t ty_v))
              ~yield:(fun t -> dec_t t ty_ret)
          in
          let t' = dec_t t ty in
          Some (t', dt', k)
      )
  in
  (* add new types' domains *)
  Ty.Map.to_seq rety.rety_domains
  |> Sequence.fold
    (fun m (ty,dom) -> M.add_finite_type m ty dom)
    m

(** {2 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name Ppb.print)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  Transform.make
    ~name
    ?on_decoded
    ~input_spec:Transform.Features.(of_list
          [Ty, Mono; Fun, Absent; Match, Absent; Ind_preds, Absent
          ])
    ~map_spec:Transform.Features.(update Ty Absent)
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
