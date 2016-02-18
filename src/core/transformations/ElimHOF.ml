
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Elimination of Higher-Order Functions} *)

module TI = TermInner
module Stmt = Statement

let name = "elim_hof"
let section = Utils.Section.make name

type 'a inv = <ty:[`Mono]; eqn:'a; ind_preds: [`Absent]>

let fpf = Format.fprintf

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module TM = TermMono.Make(T)
  module TMI = TermMono

  type term = T.t

  type decode_state = {
    dst_app_symbols: unit ID.Tbl.t;
      (* set of application symbols *)
  }

  module IntSet = CCSet.Make(CCInt)

  type arity_set = {
    as_set : IntSet.t;
    as_ty_args : term list; (* shortcut to the type arguments of the function *)
    as_ty_ret : term; (* shortcut to the return type of the function *)
  }

  let pp_arity_set out set =
    fpf out "{@[%a@]}" (IntSet.print ~start:"" ~stop:"" CCFormat.int) set.as_set

  type 'a state = {
    env: (term, term, 'a inv) Env.t;
      (* environment (to get signatures, etc.) *)
    arities: arity_set ID.Tbl.t;
      (* function symbol -> set of number of arguments it is used with *)
    decode: decode_state;
      (* bookkeeping for, later, decoding *)
  }

  (* print arity table *)
  let pp_arities out tbl =
    let pp_pair out (id,set) = fpf out "@[%a → @[%a@] (arity %d)@]"
      ID.print id pp_arity_set set (List.length set.as_ty_args)
    in
    fpf out "@[<hv>%a@]"
      (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_pair)
      (ID.Tbl.to_seq tbl)

  let create_state env = {
    arities=ID.Tbl.create 32;
    env;
    decode={
      dst_app_symbols=ID.Tbl.create 16;
    };
  }

  (* With [id : ty_args -> ty_ret], report a use of [id] with [n] arguments
     where [n <= List.length ty_args] *)
  let add_arity_ ~state id n ty_args ty_ret =
    let set =
      try ID.Tbl.find state.arities id
      with Not_found ->
        { as_set=IntSet.empty;
          as_ty_args=ty_args;
          as_ty_ret=ty_ret;
        }
    in
    let set = {set with as_set=IntSet.add n set.as_set;} in
    ID.Tbl.replace state.arities id set

  (* is [id] a function symbol? If yes, return its type arguments and return type *)
  let as_fun_ ~state id =
    let info = Env.find_exn ~env:state.env id in
    match info.Env.def with
    | Env.Fun_def _
    | Env.Fun_spec _
    | Env.Copy_abstract _
    | Env.Copy_concretize _
    | Env.NoDef ->
        let tyvars, args, ret = U.ty_unfold info.Env.ty in
        assert (tyvars=[]); (* mono, see {!inv} *)
        Some (args, ret)
    | Env.Data (_,_,_)
    | Env.Cstor (_,_,_,_) (* always fully applied *)
    | Env.Copy_ty _ -> None
    | Env.Pred (_,_,_,_,_) -> assert false (* see {!inv} *)

  (* compute set of arities for higher-order functions *)
  let compute_arities_term ~state t =
    let rec aux t = match TM.repr t with
      | TMI.Const id ->
          begin match as_fun_ ~state id with
          | Some ([], _)
          | None -> ()  (* constant, just ignore *)
          | Some (ty_args, ty_ret) ->
              (* function that is applied to 0 arguments (e.g. as a parameter) *)
              add_arity_ ~state id 0 ty_args ty_ret
          end
      | TMI.App (f, l) ->
          begin match TM.repr f with
          | TMI.Const id ->
              begin match as_fun_ ~state id with
              | Some ([],_) -> assert false
              | None -> () (* not a function *)
              | Some (ty_args, ty_ret) ->
                  assert (List.length ty_args >= List.length l);
                  add_arity_ ~state id (List.length l) ty_args ty_ret;
              end;
              (* explore subterms *)
              List.iter aux l
          | _ -> aux_rec t
          end
      | _ -> aux_rec t
    (* recurse *)
    and aux_rec t =
      U.iter () t ~f:(fun () t -> aux t) ~bind:(fun () _v -> ())
    in
    aux t

  let compute_arities_stmt ~state stmt =
    let f = compute_arities_term ~state in
    Stmt.iter stmt ~ty:f ~term:f

  (* arity set: function always fully applied?
     true iff the set contains exactly [length as_ty_args] *)
  let always_fully_applied_ set =
    assert (not (IntSet.is_empty set.as_set));
    let n = List.length set.as_ty_args in
    IntSet.mem n set.as_set && IntSet.cardinal set.as_set = 1

  let compute_arities_pb ~state pb =
    Problem.iter_statements pb ~f:(compute_arities_stmt ~state);
    (* remove functions that are always fully applied *)
    let fully_applied =
      ID.Tbl.to_seq state.arities
      |> Sequence.filter_map
        (fun (id, set) -> if always_fully_applied_ set then Some id else None)
      |> Sequence.to_rev_list
    in
    List.iter (ID.Tbl.remove state.arities) fully_applied;
    ()

  (** {2 Encoding} *)

  let elim_hof pb =
    let env = Problem.env pb in
    let state = create_state env in
    compute_arities_pb ~state pb;
    Utils.debugf ~section 3 "@[<2>arities of partially applied functions:@ @[<v>%a@]@]"
      (fun k->k pp_arities state.arities);
    (* TODO *)
    pb, state.decode

  (** {2 Decoding} *)

  let decode_model ~state:_ m = m  (* TODO *)

  (** {2 Pipe} *)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>after elimination of HOF: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name
      ~encode:(fun p ->
        let p, state = elim_hof p in
        p, state
      )
      ~decode
      ()

  let pipe ~print =
    let decode state m = decode_model ~state m in
    pipe_with ~print ~decode

end



