
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
  type ty = T.t

  (** {2 Computing Arities}

      The point here is to find, for every function symbol, the set of
      arities it is (partially) applied with.
      Only functions partially applied at least once are of interest
      in this section. *)

  module IntSet = CCSet.Make(CCInt)
  module IntMap = CCMap.Make(CCInt)

  type arity_set = {
    as_set : IntSet.t;
    as_ty_args : term list; (* shortcut to the type arguments of the function *)
    as_ty_ret : term; (* shortcut to the return type of the function *)
  }

  let pp_arity_set out set =
    fpf out "{@[%a@]}" (IntSet.print ~start:"" ~stop:"" CCFormat.int) set.as_set

  (* print arity map *)
  let pp_arities out tbl =
    let pp_pair out (id,set) = fpf out "@[%a → @[%a@]/%d@]"
      ID.print id pp_arity_set set (List.length set.as_ty_args)
    in
    fpf out "@[<hv>%a@]"
      (CCFormat.seq ~start:"" ~stop:"" ~sep:"" pp_pair)
      (ID.Map.to_seq tbl)

  (* With [id : ty_args -> ty_ret], report a use of [id] with [n] arguments
     where [n <= List.length ty_args] *)
  let add_arity_ m id n ty_args ty_ret =
    let set =
      try ID.Map.find id m
      with Not_found ->
        { as_set=IntSet.empty;
          as_ty_args=ty_args;
          as_ty_ret=ty_ret;
        }
    in
    let set = {set with as_set=IntSet.add n set.as_set;} in
    ID.Map.add id set m

  (* is [id] a function symbol? If yes, return its type arguments and return type *)
  let as_fun_ ~env id =
    let info = Env.find_exn ~env id in
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
  let compute_arities_term ~env m t =
    let rec aux m t = match TM.repr t with
      | TMI.Const id ->
          begin match as_fun_ ~env id with
          | Some ([], _)
          | None -> m  (* constant, just ignore *)
          | Some (ty_args, ty_ret) ->
              (* function that is applied to 0 arguments (e.g. as a parameter) *)
              add_arity_ m id 0 ty_args ty_ret
          end
      | TMI.App (f, l) ->
          begin match TM.repr f with
          | TMI.Const id ->
              let m = match as_fun_ ~env id with
                | Some ([],_) -> assert false
                | None -> m (* not a function *)
                | Some (ty_args, ty_ret) ->
                    assert (List.length ty_args >= List.length l);
                    add_arity_ m id (List.length l) ty_args ty_ret
              in
              (* explore subterms *)
              List.fold_left aux m l
          | _ -> aux_rec m t
          end
      | _ -> aux_rec m t
    (* recurse *)
    and aux_rec m t =
      U.fold m () t ~f:(fun m () t -> aux m t) ~bind:(fun () _v -> ())
    in
    aux m t

  let compute_arities_stmt ~env m stmt =
    let f = compute_arities_term ~env in
    Stmt.fold m stmt ~ty:f ~term:f

  (* arity set: function always fully applied?
     true iff the set contains exactly [length as_ty_args] *)
  let always_fully_applied_ set =
    assert (not (IntSet.is_empty set.as_set));
    let n = List.length set.as_ty_args in
    IntSet.mem n set.as_set && IntSet.cardinal set.as_set = 1

  let compute_arities_pb ~env pb =
    let m =
      Problem.statements pb
      |> CCVector.fold (compute_arities_stmt ~env) ID.Map.empty
    in
    (* remove functions that are always fully applied *)
    ID.Map.filter
      (fun _id set -> not (always_fully_applied_ set))
      m

  (** {2 Handle Types}

      A handle type is an abstraction of a function type. For instance,
      given [plus : nat -> (nat -> nat)], where plus is sometimes applied
      to 1 argument and sometimes to two arguments, we:
      - introduce the handle [H] that stands for [nat->nat],
      - declare that [plus : nat -> H],
      - introduce an application symbol [app_H : H -> nat -> nat],
      - replace any term of the form [plus x y] with [app_H (plus x) y] *)

  type handle =
    | H_leaf of encoded_ty (* leaf type *)
    | H_arrow of encoded_ty * handle (* [H_arrow (a,b)] reifies [a -> b] into an atomic type *)

  and encoded_ty = ET_ty of ty

  let handle_is_leaf = function
    | H_leaf _ -> true
    | H_arrow _ -> false

  let rec pp_handle out = function
    | H_leaf (ET_ty t) -> P.print out t
    | H_arrow (ET_ty t, h') -> fpf out "@[@[%a@] ·> @[%a@]@]" P.print t pp_handle h'

  (* map from handles to 'a *)
  module HandleMap = struct
    type +'a t = {
      leaves: (ty * 'a) list;  (* maps [H_leaf t] to a value, for various [t] *)
      arrows: (ty * 'a t) list; (* maps [H_arrow (t, h')] to a subtree for [h'] *)
    }

    let empty = {leaves=[]; arrows=[];}

    (* find binding for [h] in [m], or raise Not_found *)
    let rec find_exn h m = match h with
      | H_leaf (ET_ty t) -> CCList.Assoc.get_exn ~eq:U.equal m.leaves t
      | H_arrow (ET_ty t, h') ->
          let m' = CCList.Assoc.get_exn ~eq:U.equal m.arrows t in
          find_exn h' m'

    (* add [h -> v] to map [m] *)
    let rec add h v m = match h with
      | H_leaf (ET_ty t) ->
          let leaves = CCList.Assoc.set ~eq:U.equal m.leaves t v in
          {m with leaves;}
      | H_arrow (ET_ty t, h') ->
          let arrows =
            try
              let m' = CCList.Assoc.get_exn ~eq:U.equal m.arrows t in
              let m' = add h' v m' in
              CCList.Assoc.set ~eq:U.equal m.arrows t m'
            with Not_found ->
              (t, add h' v empty) :: m.arrows
          in
          {m with arrows; }
  end

  (** {2 State for Encoding and Decoding} *)

  type decode_state = {
    dst_app_symbols: unit ID.Tbl.t;
      (* set of application symbols *)
    mutable dst_handle_id: ID.t option;
      (* identifier for reifying "->" in handles *)
  }

  (* application symbol (for partial application) *)
  type apply_fun = {
    af_id: ID.t;
    af_ty: term; (* type of the function *)
    af_arity: int; (* shortcut: number of arguments *)
  }

  (* how to encode a given (partially applied) function:
     for each arity the function [f] uses, map the arity
     to a list of application symbols to use.

     A list [app1, app2, app3] means that [f x y z] will be
     encoded as [app3 (app2 (app1 x) y) z]. *)
  type fun_encoding = apply_fun list IntMap.t

  type 'a state = {
    env: (term, ty, 'a inv) Env.t;
      (* environment (to get signatures, etc.) *)
    arities: arity_set ID.Map.t;
      (* set of arities for partially applied symbols *)
    mutable app_count: int;
      (* used for generating new names *)
    mutable app_symbols: apply_fun HandleMap.t;
      (* handle type -> corresponding apply symbol *)
    mutable fun_encodings: fun_encoding ID.Map.t;
      (* partially applied function -> how to encode it *)
    mutable new_decls : (ID.t * ty) CCVector.vector;
      (* used for new declarations *)
    decode: decode_state;
      (* bookkeeping for, later, decoding *)
  }

  let pp_apply_fun out f = fpf out "@[%a :@ %a@]" ID.print f.af_id P.print f.af_ty
  let pp_fun_encoding out =
    fpf out "@[<hv>%a@]" (IntMap.print CCFormat.int (CCFormat.list pp_apply_fun))

  let create_state ~env arities = {
    env;
    arities;
    app_count=0;
    app_symbols=HandleMap.empty;
    fun_encodings=ID.Map.empty;
    new_decls=CCVector.create();
    decode={
      dst_app_symbols=ID.Tbl.create 16;
      dst_handle_id=None;
    };
  }

  (** {2 Encoding} *)

  (* TODO: afterwards: for each handle, find/introduce the corresponding
     application symbol, and add the extensionality axiom

     TODO: also proto symbol to express proto axiom *)

  let get_handle_id_ ~state = match state.decode.dst_handle_id with
    | Some i -> i
    | None ->
        let id = ID.make "to" in
        state.decode.dst_handle_id <- Some id;
        let ty_id = U.ty_arrow_l [U.ty_type; U.ty_type] U.ty_type in
        (* declare the symbol [to : type -> type -> type] *)
        CCVector.push state.new_decls (id, ty_id);
        id

  (* encode a type parameter so it becomes first-order (replace [->] with [to]) *)
  let encode_ty_ ~state t : encoded_ty =
    let rec aux t = match T.repr t with
      | TI.TyArrow (a,b) ->
          let to_ = get_handle_id_ ~state in
          U.ty_app (U.ty_const to_) [aux a; aux b]
      | _ -> U.map () t ~bind:(fun () v ->(),v) ~f:(fun () -> aux)
    in
    ET_ty (aux t)

  let ty_of_encoded_ (ET_ty t) = t
  let pp_encoded_ty_ out (ET_ty t) = P.print out t

  let encoded_arrow_l l t =
    U.ty_arrow_l (List.map ty_of_encoded_ l) (ty_of_encoded_ t)

  (* convert a handle to a proper encoded type *)
  let ty_of_handle_ ~state t : encoded_ty =
    let rec aux = function
      | H_leaf (ET_ty t) -> t
      | H_arrow (ET_ty t, h') ->
          let id = get_handle_id_ ~state in
          U.ty_app (U.const id) [t; aux h']
    in
    ET_ty (aux t)

  (* split [l] into chunks of length given by elements of [lens] minus the
     previous length. Each chunk is paired with the previous length. *)
  let rec split_chunks_ prev lens l = match lens, l with
    | [], [] -> []
    | [], _ -> [prev,l]  (* return remaining elements *)
    | len :: lens', _ ->
        let c, l' = CCList.take_drop (len-prev) l in
        (prev,c) :: split_chunks_ len lens' l'

  (* build the handle [l_1 -> ... -> l_n -> h] where the [l_i] are encoded types *)
  let rec handle_fun_ l h = match l with
    | [] -> h
    | a :: l' -> H_arrow (a, handle_fun_ l' h)

  (* number of arguments of handle *)
  let rec handle_arity_ = function
    | H_leaf _ -> 0
    | H_arrow (_, h') -> 1 + handle_arity_ h'

  let pp_decl_ out (id,ty) = fpf out "@[<2>%a :@ %a@]" ID.print id P.print ty

  (* handle -> application symbol for this handle *)
  let app_of_handle_ ~state args ret : apply_fun =
    let h = handle_fun_ args ret in
    try HandleMap.find_exn h state.app_symbols
    with Not_found ->
      let i = state.app_count in
      state.app_count <- i+1;
      let app_id = ID.make ("app_" ^ string_of_int i) in
      let ty_app = encoded_arrow_l args (ty_of_handle_ ~state ret) in
      Utils.debugf ~section 5 "@[<2>declare app_sym `@[%a :@ @[%a@]@]@]`"
        (fun k->k ID.print app_id P.print ty_app);
      CCVector.push state.new_decls (app_id, ty_app);
      let app_fun = {
        af_id=app_id;
        af_ty=ty_app;
        af_arity=handle_arity_ h;
      } in
      state.app_symbols <- HandleMap.add h app_fun state.app_symbols;
      app_fun

  (* TODO: [id] already declared, so we need to skip old decl and replace with
      new one *)

  (* for each id in arities, introduce required app symbols
     and store data structure that
     maps [arity -> sequence of apply symbs to use].
     @return a list of new type declarations *)
  let introduce_apply_syms ~state =
    ID.Map.iter
      (fun id {as_set=set; as_ty_args=ty_args; as_ty_ret=ty_ret; _} ->
        let l = IntSet.to_list set in
        (* split type arguments into "blocks" *)
        assert (List.length l <= List.length ty_args + 1); (* +1: arity 0 exists *)
        let chunks = split_chunks_ 0 l ty_args in
        Utils.debugf ~section 4 "@[<2>process %a :@ `@[%a@]`@ chunks: @[%a@]@]"
          (fun k->k ID.print id P.print (U.ty_arrow_l ty_args ty_ret)
          CCFormat.(list (pair int (list P.print))) chunks);
        let rev_chunks = List.rev chunks in
        (* traverse [rev chunks], computing the handles and declaring
           new app symbols. Note that all app symbols conceptually have
           the same type, [ty_args->ty_ret], but they place handle boundaries
             (replacing [a -> b] with [to(a,b)]) at different places.
            @param m [map int -> list app_symbols], that is [m : fun_encoding]
            @param app_l current stack of app_symbols
            @param ret_handle type of handle that is returned by chunk *)
        let rec aux m app_l ret_handle l = match l with
          | [] -> assert false
          | [(i,c)] ->
              let c = List.map (encode_ty_ ~state) c in
              (* innermost chunk: no handle, no apply. However, we need to
                 declare [id : \over{c} -> ret_handle] *)
              let ty_id = encoded_arrow_l c (ty_of_handle_ ~state ret_handle) in
              CCVector.push state.new_decls (id, ty_id);
              IntMap.add i app_l m
          | (_,[]) :: _ -> assert false   (* only last one can have 0 args *)
          | (i,(_::_ as c)) :: l' ->
              let c = List.map (encode_ty_ ~state) c in
              (* handle [\over{c} -> typof(ret_handle)] *)
              let handle' = handle_fun_ c ret_handle in
              let app_fun = app_of_handle_ ~state
                (ty_of_handle_ ~state handle' :: c) ret_handle in
              (* push app_fun onto the stack of apply functions to use *)
              let app_l = app_fun :: app_l in
              let m = IntMap.add (i+List.length c) app_l m in
              aux m app_l handle' l'
        in
        (* map i->app_i *)
        let m = aux IntMap.empty [] (H_leaf (encode_ty_ ~state ty_ret)) rev_chunks in
        Utils.debugf ~section 4 "@[<2>map %a to@ %a@]"
          (fun k->k ID.print id pp_fun_encoding m);
        state.fun_encodings <- ID.Map.add id m state.fun_encodings
      )
      state.arities;
    (* obtain new declarations *)
    let decls = CCVector.to_list state.new_decls in
    CCVector.clear state.new_decls;
    decls

  (* eliminate partial applications in the given statement. Can return several
     statements because of the declarations of new application symbols. *)
  let elim_hof_statement ~state stmt =
    let info = Stmt.info stmt in
    match Stmt.view stmt with
    | Stmt.Decl (id,decl,ty,attrs) ->
        if ID.Map.mem id state.arities
        then (
          (* change type, with a handle type *)
          (*
          try
            let handle_ty = ID.Tbl.find state.handles

          *)
          assert false (* TODO *)

        )
        else
          (* keep as is, not a partially applied fun *)
          [Stmt.mk_decl ~info id decl ty ~attrs]
    | Stmt.Axiom ax -> [stmt]
    | Stmt.TyDef (_,_)
    | Stmt.Pred (_,_,_)
    | Stmt.Copy _
    | Stmt.Goal _ -> assert false (* TODO *)

  let elim_hof pb =
    let env = Problem.env pb in
    (* compute arities *)
    let arities = compute_arities_pb ~env:env pb in
    Utils.debugf ~section 3 "@[<2>arities of partially applied functions:@ @[<v>%a@]@]"
      (fun k->k pp_arities arities);
    (* introduce application symbols and sorts *)
    let state = create_state ~env arities in
    Utils.debug ~section 3 "introduce application symbols and handle types…";
    let decls_app = introduce_apply_syms ~state in
    Utils.debugf ~section 3 "@[<2>new declarations:@ @[<v>%a@]@]"
      (fun k->k CCFormat.(list ~start:"" ~stop:"" ~sep:"" pp_decl_) decls_app);
    let pb' = Problem.flat_map_statements pb ~f:(elim_hof_statement ~state) in
    (* return new problem *)
    pb', state.decode

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



