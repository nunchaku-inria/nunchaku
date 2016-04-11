
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Compute the cardinality of Types} *)

module TI = TermInner
module Stmt = Statement

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

(** Approximation of a cardinal, including infinite cardinals *)
module Card = struct
  type t =
    | Exact of Z.t

    | QuasiFiniteGEQ of Z.t
        (** unknown, but ≥ 0. If all uninterpreted types are finite, then
            this is finite too *)

    | Infinite

    | Unknown
        (** Any value, we do not know *)

  let (+) a b = match a, b with
    | Unknown, _
    | _, Unknown -> Unknown
    | QuasiFiniteGEQ a, (QuasiFiniteGEQ b | Exact b)
    | Exact a, QuasiFiniteGEQ b -> QuasiFiniteGEQ Z.(a+b)
    | Exact a, Exact b -> Exact Z.(a+b)
    | Infinite, _
    | _, Infinite -> Infinite (* even infinite+unknown = infinite *)

  let zero = Exact Z.zero

  let one = Exact Z.one
  let of_int i = Exact (Z.of_int i)
  let of_z i = Exact i
  let quasi_finite_geq n = QuasiFiniteGEQ n
  let quasi_finite_zero = QuasiFiniteGEQ Z.zero
  let quasi_finite_nonzero = QuasiFiniteGEQ Z.one
  let infinite = Infinite
  let unknown = Unknown
  let is_zero = function Exact z -> Z.sign z = 0 | _ -> false

  let ( * ) a b = match a, b with
    | Unknown, _
    | _, Unknown -> Unknown
    | Exact x, _
    | _, Exact x when Z.sign x = 0 -> zero (* absorption by 0 *)
    | (QuasiFiniteGEQ z, _ | _, QuasiFiniteGEQ z) when Z.sign z = 0 ->
        quasi_finite_zero (* [0,∞] *)
    | Infinite, _
    | _, Infinite ->
        (* we know the other param is not 0 and does not contain 0 *)
        Infinite
    | Exact a, Exact b -> Exact Z.(a*b)
    | QuasiFiniteGEQ a, (Exact b | QuasiFiniteGEQ b)
    | Exact a, QuasiFiniteGEQ b -> QuasiFiniteGEQ Z.(a * b)  (* absorbs bounded *)

  let equal a b = match a, b with
    | Unknown, Unknown -> true
    | QuasiFiniteGEQ a, QuasiFiniteGEQ b
    | Exact a, Exact b -> Z.equal a b
    | Infinite, Infinite -> true
    | Unknown, _
    | Infinite, _
    | QuasiFiniteGEQ _, _
    | Exact _, _ -> false

  let hash = function
    | Exact x -> Z.hash x
    | QuasiFiniteGEQ z -> Hashtbl.hash (13, Z.hash z)
    | Unknown -> 13
    | Infinite -> 17
  let hash_fun x = CCHash.int (hash x)

  let print out = function
    | Unknown -> CCFormat.string out "<unknown>"
    | Exact x -> Z.pp_print out x
    | QuasiFiniteGEQ z -> Format.fprintf out "[%a,∞]" Z.pp_print z
    | Infinite -> CCFormat.string out "ω"
end

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type ty = T.t
  type ('a, 'inv) env = ('a, ty, 'inv) Env.t constraint 'inv = <ty:[`Mono]; ..>

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
    TyTbl.add cache.state ty (Cached card)

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

  (* evaluate the cardinality of [ty] *)
  let rec eval_ty_
    : save_op -> (_,_) env -> cache -> ty -> Card.t
    = fun op env cache ty ->
      match TyTbl.get cache.state ty with
      | Some (Cached c)
      | Some (Assume c) -> c
      | None ->
        match T.repr ty with
        | TI.Const id -> eval_id_ op env cache id
        | _ -> Card.quasi_finite_nonzero (* approx *)

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
          (* TODO: check attributes *)
          Card.quasi_finite_nonzero
      | Env.Cstor _
      | Env.Fun_def (_,_,_)
      | Env.Fun_spec (_,_)
      | Env.Pred (_,_,_,_,_)
      | Env.Copy_abstract _
      | Env.Copy_concrete _ -> errorf_ "%a is not a type" ID.print id
    in
    (* maybe cache *)
    begin match op with
      | Save ->
          Utils.debugf ~section 5 "@[<2>card `@[%a@]` =@ %a@]"
            (fun k->k ID.print id Card.print res);
          save_ cache (U.ty_const id) res
      | Do_not_save -> ()
    end;
    res

  let cardinality_ty_id ?(cache=create_cache ()) env id =
    eval_id_ Save env cache id

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
