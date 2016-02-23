
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
  module PStmt = Stmt.Print(P)(P)
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

  and encoded_ty = ty

  let handle_is_leaf = function | H_leaf _ -> true | H_arrow _ -> false
  let handle_is_fun = function H_leaf _ -> false | H_arrow _ -> true
  let handle_leaf x = H_leaf x
  let handle_arrow x y = H_arrow (x,y)

  let rec pp_handle out = function
    | H_leaf t -> P.print out t
    | H_arrow (t, h') -> fpf out "@[@[%a@] ·> @[%a@]@]" P.print t pp_handle h'

  (* map from handles to 'a *)
  module HandleMap = struct
    type +'a t = {
      leaves: (ty * 'a) list;  (* maps [H_leaf t] to a value, for various [t] *)
      arrows: (ty * 'a t) list; (* maps [H_arrow (t, h')] to a subtree for [h'] *)
    }

    let empty = {leaves=[]; arrows=[];}

    (* find binding for [h] in [m], or raise Not_found *)
    let rec find_exn h m = match h with
      | H_leaf t -> CCList.Assoc.get_exn ~eq:U.equal m.leaves t
      | H_arrow (t, h') ->
          let m' = CCList.Assoc.get_exn ~eq:U.equal m.arrows t in
          find_exn h' m'

    (* add [h -> v] to map [m] *)
    let rec add h v m = match h with
      | H_leaf t ->
          let leaves = CCList.Assoc.set ~eq:U.equal m.leaves t v in
          {m with leaves;}
      | H_arrow (t, h') ->
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
  type fun_encoding = {
    fe_stack: apply_fun list IntMap.t;
    fe_args: ty list; (* type arguments used to return the first handle *)
    fe_ret_handle: handle; (* handle type returned by the function *)
  }

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

  let pp_apply_fun out f =
    fpf out "@[<2>%a/%d :@ `@[%a@]`@]" ID.print f.af_id f.af_arity P.print f.af_ty

  let pp_app_funs out =
    fpf out "[@[%a@]]" (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_apply_fun)

  let pp_fun_encoding out =
    fpf out "[@[<v>%a@]]"
      (IntMap.print ~start:"" ~stop:"" ~sep:"" ~arrow:" -> " CCFormat.int pp_app_funs)

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
    aux t

  (* convert a handle to a proper encoded type *)
  let ty_of_handle_ ~state t : encoded_ty =
    let rec aux = function
      | H_leaf t -> t
      | H_arrow (t, h') ->
          let id = get_handle_id_ ~state in
          U.ty_app (U.const id) [t; aux h']
    in
    aux t

  (* build the handle [l_1 -> ... -> l_n -> h] where the [l_i] are encoded types *)
  let rec handle_arrow_l l h = match l with
    | [] -> h
    | a :: l' -> H_arrow (a, handle_arrow_l l' h)

  let pp_decl_ out (id,ty) = fpf out "@[<2>%a :@ %a@]" ID.print id P.print ty

  (* handle -> application symbol for this handle *)
  let app_of_handle_ ~state args ret : apply_fun =
    let h = handle_arrow_l args ret in
    try HandleMap.find_exn h state.app_symbols
    with Not_found ->
      let i = state.app_count in
      state.app_count <- i+1;
      let app_id = ID.make ("app_" ^ string_of_int i) in
      let ty_app = U.ty_arrow_l args (ty_of_handle_ ~state ret) in
      Utils.debugf ~section 5 "@[<2>declare app_sym `@[%a :@ @[%a@]@]@]`"
        (fun k->k ID.print app_id P.print ty_app);
      CCVector.push state.new_decls (app_id, ty_app);
      let app_fun = {
        af_id=app_id;
        af_ty=ty_app;
        af_arity=List.length args;
      } in
      state.app_symbols <- HandleMap.add h app_fun state.app_symbols;
      app_fun

  (* split [l] into chunks of length given by elements of [lens] minus the
     previous length. Each chunk is paired with
     the remaining set of arguments. *)
  let rec split_chunks_ prev lens l = match lens, l with
    | [], [] -> []
    | [], _ -> [l,[]]  (* return remaining elements *)
    | len :: lens', _ ->
        let c, l' = CCList.take_drop (len-prev) l in
        (c,l') :: split_chunks_ len lens' l'

  let pp_chunks out =
    let pp_tys out = fpf out "@[%a@]" CCFormat.(list P.print) in
    let pp_pair out (a,b) = fpf out "@[(%a, remaining %a)@]" pp_tys a pp_tys b in
    fpf out "[@[%a@]]" CCFormat.(list ~start:"" ~stop:"" pp_pair)

  (* introduce/get required app symbols for the given ID
     and store data structure that maps [arity -> sequence of apply symbs to use].
     @return the fun encoding for ID *)
  let introduce_apply_syms ~state id =
    let {as_set=set; as_ty_args=ty_args; as_ty_ret=ty_ret; _} =
      try ID.Map.find id state.arities
      with Not_found -> assert false
    in
    let l = IntSet.to_list set in
    let n = List.length ty_args in
    (* split type arguments into "blocks" *)
    assert (List.length l <= n + 1); (* +1: arity 0 exists *)

    (* encode type arguments and return type *)
    let ty_args = List.map (encode_ty_ ~state) ty_args in
    let ty_ret = encode_ty_ ~state ty_ret in

    let chunks = split_chunks_ 0 l ty_args in
    Utils.debugf ~section 4 "@[<2>process %a :@ `@[%a@]`@ chunks: @[%a@]@]"
      (fun k->k
        ID.print id P.print (U.ty_arrow_l ty_args ty_ret) pp_chunks chunks);

    (* special case for first chunk, which doesn't need an application
       symbol *)
    let first_args, first_handle, n_args, m, chunks' =
      match chunks with
      | [] -> assert false
      | (args, remaining_args) :: chunks' ->
          (* first application: no app symbol *)
          let m = IntMap.singleton (List.length args) [] in
          let handle =
            handle_arrow_l args
              (handle_arrow_l remaining_args (H_leaf ty_ret))
            |> ty_of_handle_ ~state |> handle_leaf in
          args, handle, List.length args, m, chunks'
    in
    (* deal with remaining chunks. For each chunk we need the handle
       returned by the previous chunks (that is, if we apply arguments
       that come earlier, which handle type do we get?) *)
    let _, _, _, m =
      List.fold_left
        (fun (prev_handle, n_args, app_l, m) chunk ->
          (* we already applied the function to [n_args] using [app_l] *)
          let args, remaining_args = chunk in
          (* not the initial application: need an app symbol.
             type of app symbol is
              [handle :=  args -> (remaining_args to ty_ret)] *)
          let handle_ret = handle_arrow_l remaining_args (H_leaf ty_ret) in
          let args' = ty_of_handle_ ~state prev_handle :: args in
          let app_fun = app_of_handle_ ~state args' handle_ret in
          let n_args' = List.length args + n_args in
          let app_l' = app_fun :: app_l in
          let m = IntMap.add n_args' (List.rev app_l') m in
          (* return handle_ret, because it is the type obtained by
             fully applying [app_fun] *)
          handle_ret, n_args', app_l', m
        )
        (first_handle, n_args, [], m)
        chunks'
    in
    Utils.debugf ~section 4 "@[<hv2>map %a to@ %a@]"
      (fun k->k ID.print id pp_fun_encoding m);

    let fe = {
      fe_stack=m;
      fe_args=first_args;
      fe_ret_handle=first_handle;
    } in

    state.fun_encodings <- ID.Map.add id fe state.fun_encodings;
    fe

  (* apply the list of apply_fun to [l]. Arities should match. *)
  let rec apply_app_funs_ stack l =
    Utils.debugf ~section 5 "@[<2>apply_stack@ @[%a@]@ to @[%a@]@]"
      (fun k->k pp_app_funs stack (CCFormat.list P.print) l);
    match stack with
    | [] -> assert false
    | [f] ->
        assert (f.af_arity = List.length l);
        U.app (U.const f.af_id) l
    | f :: stack' ->
        assert (f.af_arity >= 1);
        let args, l' = CCList.take_drop f.af_arity l in
        assert (List.length args = f.af_arity);
        (* compute closure, then push it on l *)
        let closure =  U.app (U.const f.af_id) args in
        apply_app_funs_ stack' (closure :: l')

  (* traverse [t] and replace partial applications with fully applied symbols
      from state.app_symbols. Also encodes every type using [handle_id] *)
  let elim_hof_term ~state t =
    let rec aux subst t = match T.repr t with
      | TI.Var v -> Var.Subst.find_exn ~subst v |> U.var
      | TI.TyArrow _ -> aux_ty subst t (* type: encode it *)
      | TI.App (f,l) ->
          begin match T.repr f with
          | TI.Const id when ID.Map.mem id state.fun_encodings ->
              let l = List.map (aux subst) l in
              (* replace by applications symbols, based on [length l] *)
              let n = List.length l in
              let fun_encoding = ID.Map.find id state.fun_encodings in
              (* stack of application functions to use *)
              let app_l = IntMap.find n fun_encoding.fe_stack in
              apply_app_funs_ app_l (f::l)
          | _ -> aux' subst t
          end
      | TI.Bind _
      | TI.Let _
      | TI.Match _
      | TI.Const _
      | TI.Builtin _
      | TI.TyBuiltin _
      | TI.TyMeta _ -> aux' subst t
    (* traverse subterms of [t] *)
    and aux' subst t =
      U.map subst t ~f:aux
      ~bind:(fun subst v ->
        (* replace [v] with [v'], which has an encoded type *)
        let v' = Var.update_ty v ~f:(aux_ty subst) in
        let subst = Var.Subst.add ~subst v v' in
        subst, v')
    and aux_ty subst ty = encode_ty_ ~state (U.eval_renaming ~subst ty) in
    aux Var.Subst.empty t

  (* eliminate partial applications in the given statement. Can return several
     statements because of the declarations of new application symbols. *)
  let elim_hof_statement ~state stmt =
    let info = Stmt.info stmt in
    let tr_term = elim_hof_term ~state in
    let tr_type = encode_ty_ ~state in
    match Stmt.view stmt with
    | Stmt.Decl (id,decl,ty,attrs) ->
        if ID.Map.mem id state.arities
        then (
          Utils.debugf ~section 3
            "introduce application symbols and handle types for %a…"
            (fun k->k ID.print id);
          let fun_encoding = introduce_apply_syms ~state id in
          let ty' = U.ty_arrow_l fun_encoding.fe_args
            (ty_of_handle_ ~state fun_encoding.fe_ret_handle) in
          Utils.debugf ~section 4 "@[<2>fun %a now has type `@[%a@]`@]"
            (fun k->k ID.print id P.print ty');
          let stmt = Stmt.mk_decl ~info id decl ty' ~attrs in
          (* obtain new type declarations *)
          let stmts' =
            CCVector.map
              (fun (app_id,app_ty) ->
                Stmt.mk_decl ~info ~attrs:[] app_id decl app_ty)
              state.new_decls
            |> CCVector.to_list
          in
          CCVector.clear state.new_decls;
          Utils.debugf ~section 3 "@[<2>new declarations:@ @[<v>%a@]@]"
            (fun k->k (CCFormat.list ~start:"" ~stop:"" ~sep:"" PStmt.print) stmts');
          stmts' @ [stmt]
        )
        else
          (* keep as is, not a partially applied fun *)
          [Stmt.mk_decl ~info id decl ty ~attrs]
    | Stmt.Axiom _
    | Stmt.TyDef (_,_)
    | Stmt.Pred (_,_,_)
    | Stmt.Copy _
    | Stmt.Goal _ ->
        [Stmt.map ~term:tr_term ~ty:tr_type stmt] (* TODO *)

  let elim_hof pb =
    let env = Problem.env pb in
    (* compute arities *)
    let arities = compute_arities_pb ~env:env pb in
    Utils.debugf ~section 3 "@[<2>arities of partially applied functions:@ @[<v>%a@]@]"
      (fun k->k pp_arities arities);
    (* introduce application symbols and sorts *)
    let state = create_state ~env arities in
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



