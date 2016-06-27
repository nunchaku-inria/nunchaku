
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner
module Stmt = Statement

module Z = Cardinality.Z
module Card = Cardinality

exception Error of string

exception Polymorphic

exception EmptyData of ID.t

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf msg ~f:error_

let section = Utils.Section.make "ty_cardinality"

let () = Printexc.register_printer
  (function
    | Error msg -> Some (Utils.err_sprintf "ty cardinality: %s" msg)
    | Polymorphic -> Some (Utils.err_sprintf "type is polymorphic")
    | EmptyData id -> Some (Utils.err_sprintf "data %a is empty" ID.print id)
    | _ -> None)

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type ty = T.t
  type 'a env = ('a, ty) Env.t

  module TyTbl = CCHashtbl.Make(struct
    type t = T.t
    let equal = U.equal
    let hash = U.hash
  end)

  type cache_state =
    | Cached of Card.t
    | Assume of Card.t (* locally assume some cardinality *)

  (* cache: maps IDs to (fully computed) cardinalities *)
  type cache = {
    state: cache_state TyTbl.t; (** main state *)
    non_zero: unit ID.Tbl.t; (** types we know are non-empty data *)
  }

  let create_cache () = {
    state=TyTbl.create 16;
    non_zero=ID.Tbl.create 8;
  }

  let save_ cache ty card =
    assert (not (TyTbl.mem cache.state ty));
    TyTbl.replace cache.state ty (Cached card)

  (* enter the given state for [ty], calling [f ()], and returns the
     same as [f ()]. It cleans up the state afterwards *)
  let enter_ty_ cache ty state ~f =
    assert (not (TyTbl.mem cache.state ty));
    TyTbl.add cache.state ty state;
    CCFun.finally ~f ~h:(fun () -> TyTbl.remove cache.state ty)

  let enter_id_ cache id state ~f = enter_ty_ cache (U.ty_const id) state ~f

  let sum_ ~f l = ID.Map.fold (fun _ x acc -> Card.(acc+f x)) l Card.zero
  let product_ ~f l = List.fold_left (fun acc x -> Card.(acc*f x)) Card.one l

  type save_op =
    | Save
    | Do_not_save

  (* evaluate the cardinality of [ty], using the cache *)
  let rec eval_ty_
    : save_op -> _ env -> cache -> ty -> Card.t
    = fun op env cache ty ->
      match TyTbl.get cache.state ty with
      | Some (Cached c)
      | Some (Assume c) -> c
      | None ->
        let res = match T.repr ty with
          | TI.Const id -> eval_id_ op env cache id
          | _ -> Card.quasi_finite_nonzero (* approx *)
        in
        (* maybe cache *)
        begin match op with
          | Save ->
            Utils.debugf ~section 5 "@[<2>card `@[%a@]` =@ %a@]"
              (fun k->k P.print ty Card.print res);
            save_ cache ty res
          | Do_not_save -> ()
        end;
        res

  (* compute the sum of products of cardinalities of [def]'s constructors
     type arguments, under the assumption [assume] for [def.ty_id] *)
  and compute_sum_ op env cache def assume =
    let id = def.Stmt.ty_id in
    enter_id_ cache id assume
      ~f:(fun () ->
        sum_ def.Stmt.ty_cstors
          ~f:(fun cstor ->
            product_ cstor.Stmt.cstor_args
              ~f:(eval_ty_ op env cache)))

  (* check that [d] is not an empty data.
      @raise EmptyData otherwise *)
  and check_non_zero_ env cache d =
    let id = d.Stmt.ty_id in
    if not (ID.Tbl.mem cache.non_zero id) then (
      (* eval definition of [d] assuming its cardinal is 0. If we find 0,
         then the type is empty and we raise *)
      let c = compute_sum_ Do_not_save env cache d (Assume Card.zero) in
      if Card.is_zero c then raise (EmptyData d.Stmt.ty_id);
      (* remember for later *)
      ID.Tbl.add cache.non_zero id ()
    )

  (* eval the cardinality of the given type *)
  and eval_id_ op env cache id =
    let info = Env.find_exn ~env id in
    (* only monomorphic types are accepted *)
    if not (U.ty_is_Type info.Env.ty) then raise Polymorphic;
    let res = match Env.def info with
      | Env.Data (`Data,_,def) ->
          (* check [def] is not an empty data *)
          check_non_zero_ env cache def;
          compute_sum_ op env cache def (Assume Card.infinite)
      | Env.Data (`Codata,_,def) ->
          (* first approximation *)
          let approx =
            compute_sum_ Do_not_save env cache def (Assume Card.one)
          in
          begin match approx with
            | Card.Exact z when Z.equal z Z.one ->
                (* special case: unary codata, such as [stream] *)
                Card.one
            | Card.QuasiFiniteGEQ z when Z.compare z Z.one <= 0 ->
                (* we do not know whether this is 0, 1 or more *)
                Card.unknown
            | _ ->
                (* regular computation of the sum of products of constructors.
                   Since cardinal is not one, we can assume it's +∞ *)
                compute_sum_ op env cache def (Assume Card.infinite)
          end
      | Env.Copy_ty c ->
          begin match c.Stmt.copy_pred with
          | Some _ -> Card.quasi_finite_zero (* restriction of size? *)
          | None -> eval_ty_ op env cache c.Stmt.copy_of (* cardinality of definition *)
          end
      | Env.NoDef ->
          let attrs = info.Env.decl_attrs in
          CCList.find_map
            (function
              | Stmt.Attr_card_min n ->
                Some (Card.QuasiFiniteGEQ (Z.of_int n))
              | Stmt.Attr_infinite -> Some Card.infinite
              | Stmt.Attr_card_hint c -> Some c
              | _ -> None)
            attrs
          |> CCOpt.get Card.quasi_finite_nonzero
      | Env.Cstor _
      | Env.Fun_def (_,_,_)
      | Env.Fun_spec (_,_)
      | Env.Pred (_,_,_,_,_)
      | Env.Copy_abstract _
      | Env.Copy_concrete _ -> errorf_ "%a is not a type" ID.print id
    in
    res

  let cardinality_ty_id ?(cache=create_cache ()) env id =
    eval_ty_ Save env cache (U.ty_const id)

  let cardinality_ty ?(cache=create_cache()) env ty =
    eval_ty_ Save env cache ty

  let check_non_zero ?(cache=create_cache()) env stmt =
    match Stmt.view stmt with
    | Stmt.TyDef (`Data, l) ->
        Utils.debugf ~section 5 "@[<2>check well-formed:@ `@[%a@]`@]"
          (fun k->
            let module PStmt = Stmt.Print(P)(P) in
            k PStmt.print_tydefs (`Data,l));
        List.iter (check_non_zero_ env cache) l
    | _ -> ()

  let rec is_incomplete env ty = match T.repr ty with
    | TI.Const id ->
      let info = Env.find_exn ~env id in
      Env.is_incomplete info
    | _ ->
      (* "or" on subtypes *)
      U.fold false () ty ~bind:(fun () _ -> ())
        ~f:(fun b () ty -> b || is_incomplete env ty)

  (* TODO *)
  let is_abstract _ _ =
    Utils.not_implemented "AnalyzeType.is_abstract"
end
