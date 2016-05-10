
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

type state = {
  mutable ty_to_pred: ID.t Ty.Map.t;
    (* type -> predicate for this type *)
  mutable pred_to_ty: T.t ID.Map.t;
    (* predicate -> type it encodes *)
  parametrized_ty: unit ID.Tbl.t;
    (* parametrized ty *)
  dummy_ty: T.t;
    (* dummy "universal" type *)
}

let create_state ~dummy_ty () = {
  ty_to_pred=Ty.Map.empty;
  pred_to_ty=ID.Map.empty;
  parametrized_ty=ID.Tbl.create 16;
  dummy_ty;
}

(* find predicate for this type
   precondition: [t] a type for which we created a new predicate *)
let find_pred state t =
  assert (Ty.is_ty t);
  Ty.Map.find t state.ty_to_pred

let encode_var state subst v =
  let v' = Var.fresh_copy v |> Var.set_ty ~ty:state.dummy_ty in
  let subst = Var.Subst.add ~subst v v' in
  subst, v'

let rec encode_term state subst t = match T.repr t with
  | TI.Var v -> U.var (Var.Subst.find_exn ~subst v)
  | TI.Bind ((`Forall | `Exists) as b, v, body) ->
    let p = find_pred state (Var.ty v) in
    let subst, v' = encode_var state subst v in
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
    U.map subst t ~f:(encode_term state) ~bind:(encode_var state)

(* types are all sent to [state.dummy_ty] *)
let encode_ty state _ t =
  assert (Ty.is_ty t);
  assert (Ty.Map.mem t state.ty_to_pred);
  state.dummy_ty

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

(* ensure the type maps to some predicate *)
let ensure_maps_to_predicate state ty =
  if not (Ty.Map.mem ty state.ty_to_pred)
  then (
    match Ty.repr ty with
      | TyI.Const id ->
        errorf_ "atomic type `%a` should have been mapped to a predicate" ID.print id
      | TyI.Arrow _ -> assert false
      | TyI.Builtin `Unitype ->
        () (* no need to declare *)
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
  )

let encode_stmt state st =
  Utils.debugf ~section 3 "@[<2>encode statement@ `@[%a@]`@]"
    (fun k->k PStmt.print st);
  let info = Stmt.info st in
  match Stmt.view st with
  | Stmt.Decl (id, ty, _) when U.ty_returns_Type ty ->
    (* type declaration *)
    let _, args, _ = U.ty_unfold ty in
    assert (List.for_all U.ty_is_Type args);
    begin match args with
      | [] ->
        (* atomic type, easy *)
        let p = ID.make_f "is_%a" ID.print_name id in
        add_pred_ state (U.const id) p
      | _::_ ->
        (* not atomic, we need to declare each instance later *)
        ID.Tbl.add state.parametrized_ty id ();
    end;
    [] (* remove statement *)
  | Stmt.Decl (id, ty, attrs) when U.ty_returns_Prop ty ->
    let _, args, _ = U.ty_unfold ty in
    List.iter (ensure_maps_to_predicate state) args;
    (* new type [term -> term -> ... -> term -> prop] *)
    let ty' =
      U.ty_arrow_l
        (List.map (fun _ -> U.ty_builtin `Unitype) args)
        U.ty_prop
    in
    [ Stmt.decl ~info ~attrs id ty']
  | Stmt.Decl (id, ty, attrs) ->
    let _, args, ret = U.ty_unfold ty in
    (* declare every argument type, + the return type *)
    ensure_maps_to_predicate state ret;
    List.iter (ensure_maps_to_predicate state) args;
    (* new type [term -> term -> ... -> term -> term] *)
    let ty' =
      U.ty_arrow_l
        (List.map (fun _ -> U.ty_builtin `Unitype) args)
        (U.ty_builtin `Unitype)
    in
    [ Stmt.decl ~info ~attrs id ty']
  | _ ->
    [Stmt.map_bind Var.Subst.empty st
      ~term:(encode_term state)
      ~ty:(encode_ty state)
      ~bind:Var.Subst.rename_var]

let transform_pb pb =
  let dummy_ty = U.ty_builtin `Unitype in
  let state = create_state ~dummy_ty () in
  let pb' = Problem.flat_map_statements pb ~f:(encode_stmt state) in
  pb', state

let decode_model ~state:_ m = m (* TODO *)

let pipe_with ~decode ~print ~check:_ =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after ElimTypes@}: %a@]@." Ppb.print)
  in
  Transform.make
    ~name
    ~on_encoded
    ~encode:transform_pb
    ~decode
    ()

let pipe ~print ~check =
  pipe_with ~check ~print
    ~decode:(fun state -> Problem.Res.map_m ~f:(decode_model ~state))
