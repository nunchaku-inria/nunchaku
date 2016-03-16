
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Specialization} *)

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst

type id = ID.t
type 'a var = 'a Var.t
type inv = <eqn:[`Single]; ty:[`Mono]; ind_preds:[`Absent]>

let name = "specialize"
let fpf = Format.fprintf

exception Error of string

let () = Printexc.register_printer
  (function
    | Error msg -> Some ("error in specialization: " ^ msg)
    | _ -> None)

let error_ msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf ~f:error_ msg
let section = Utils.Section.make name

(* Call graph: tracks recursive calls between several functions,
   where arguments are variables. Calling a function with a non-variable
   points to the junk state [Non_identical] *)
module CallGraph = struct
  type node =
    | Arg of ID.t * int  (* [f, n] is [n]-th argument of function [f] *)
    | Non_identical (* an argument of non-variable form, or another variable *)

  let node_equal a b = match a,b with
    | Arg (i1,n1), Arg (i2,n2) -> ID.equal i1 i2 && n1=n2
    | Non_identical, Non_identical -> true
    | Arg _, Non_identical
    | Non_identical, Arg _ -> false

  let node_hash = function
    | Non_identical -> 3
    | Arg(id,n) -> Hashtbl.hash (ID.hash id, Hashtbl.hash n)

  module IDIntTbl = CCHashtbl.Make(struct
    type t = node
    let equal = node_equal
    let hash = node_hash
  end)

  type reachability =
    | R_not_computed
    | R_reachable
    | R_not_reachable

  type cell = {
    mutable cell_children: node list;
    mutable cell_reaches_nonidentical: reachability; (* nonvar is reachable from cell? *)
  }

  type t = cell IDIntTbl.t

  let create () = IDIntTbl.create 16

  (* add an arrow n1->n2 *)
  let add g n1 n2 =
    try
      let c = IDIntTbl.find g n1 in
      if not (CCList.Set.mem ~eq:node_equal n1 c.cell_children)
      then c.cell_children <- n1 :: c.cell_children;
    with Not_found ->
      IDIntTbl.add g n1
        {cell_children=[n2]; cell_reaches_nonidentical=R_not_computed; }

  let add_call g n1 i1 n2 i2 = add g (Arg (n1,i1)) (Arg (n2,i2))
  let add_nonidentical g n1 i1 = add g (Arg(n1,i1)) Non_identical

  (* can we reach [Non_identical] from [n1] following edges of [g]? *)
  let can_reach_nonidentical g n1 =
    let rec aux n =
      n=Non_identical ||
      try
        let c = IDIntTbl.find g n in
        match c.cell_reaches_nonidentical with
          | R_reachable -> true
          | R_not_reachable -> false
          | R_not_computed ->
              (* first, avoid looping *)
              c.cell_reaches_nonidentical <- R_not_reachable;
              let res = List.exists aux c.cell_children in
              if res then c.cell_reaches_nonidentical <- R_reachable;
              res
      with Not_found -> false
    in
    aux n1

  (* view [t] as a graph *)
  let as_graph g =
    let children n =
      try IDIntTbl.find g n |> Sequence.of_list
      with Not_found -> Sequence.empty
    in
    CCGraph.make_tuple children

  let print out g =
    let pp_node out = function
      | Non_identical -> CCFormat.string out "<non-identical>"
      | Arg (id,n) -> fpf out "arg(%a,%d)" ID.print id n
    in
    let pp_pair out (n,c) =
      fpf out "@[<2>%a ->@ [@[%a@]]@]"
        pp_node n (CCFormat.list ~start:"" ~stop:"" pp_node) c.cell_children
    in
    fpf out "@[<v2>graph {@,@[<v>%a@]@,}@]"
      (CCFormat.seq ~start:"" ~stop:"" pp_pair) (IDIntTbl.to_seq g)
end

module Make(T : TI.S) = struct
  module P = TI.Print(T)
  module U = TI.Util(T)
  module PStmt = Statement.Print(P)(P)
  module Red = Reduce.Make(T)
  module VarSet = Var.Set(T)

  type term = T.t
  type ty = term

  (** Specialization of a function is parametrized by a set of (fixed)
      arguments of the function *)
  module Arg : sig
    include Traversal.ARG
    val empty : t
    val is_empty : t -> bool
    val length : t -> int
    val to_list : t -> (int * T.t) list
    val make : (int * T.t) list -> t
  end = struct
    type t = (int * T.t) list (* sorted *)

    let empty = []
    let is_empty = function [] -> true | _::_ -> false
    let length = List.length
    let make l = List.sort (fun (i,_)(j,_) -> Pervasives.compare i j) l
    let to_list l = l

    let rec equal l1 l2 = match l1, l2 with
      | [], [] -> true
      | [], _ | _, [] -> false
      | (i1,t1) :: l1', (i2,t2) :: l2' ->
          i1 = i2 && U.equal t1 t2 && equal l1' l2'

    let hash_fun = CCHash.(list (pair int U.hash_fun))
    let hash = CCHash.apply hash_fun

    let print out l =
      let pp_pair out (i,t) = fpf out "@[%d -> %a@]" i P.print t in
      fpf out "[@[<hv>%a@]]" (CCFormat.list ~start:"" ~stop:"" pp_pair) l
    let section = section
    let fail = errorf
  end

  type new_fun = {
    nf_id: ID.t;  (* name of new function *)
    nf_ty: ty;
    nf_specialized_from: ID.t; (* source *)
    (* TODO: also add info on which arguments have been specialized/kept *)
  }

  type decode_state = term ID.Tbl.t
  (* TODO: this should contain a bit more information,
     including `fun_id -> (fun_id * Arg.t)` to know that a function is
     another function specialized on some arguments *)

  (* TODO: during direct traversal, look at "rec" definitions and compute
     the subset of arguments which remain the same through every recursive
     calls of the function. Those arguments are the only ones on which
     the function can be specialized.

     Then use this information during the specialization *)

  type 'a state = {
    specializable_args : bool array ID.Tbl.t;
      (* function -> list of argument positions that can be specialized *)
    new_funs: (Arg.t * new_fun) list ID.Tbl.t;
      (* maps [f] to a list of [args_i, f'], where each [f'] is
          a specialization of [f] on [args_i].
          [f'] has a type that should allow it to be applied to [map snd args_i] *)
    mutable count: int;
      (* used for new names *)
    mutable fun_ : (depth:int -> ID.t -> Arg.t -> unit);
      (* the function used to specialize [id] on [arg] *)
    mutable get_env : (unit -> (term, term, 'a) Env.t);
      (* obtain the environment *)
    decode: decode_state;
      (* used for decoding new symbols *)
    new_decls: (term, ty, inv) Stmt.t CCVector.vector;
      (* vector of new declarations *)
  }

  let create_state () = {
    specializable_args=ID.Tbl.create 32;
    new_funs=ID.Tbl.create 32;
    count=0;
    decode=ID.Tbl.create 32;
    fun_ = (fun ~depth:_ _ _ -> assert false);
    get_env = (fun _ -> assert false);
    new_decls=CCVector.create();
  }

  (* obtain the list of type arguments *)
  let get_ty_args_ ty =
    let _, args, _ = U.ty_unfold ty in
    args

  (* compute the set of specializable arguments in each function of [defs] *)
  let compute_specializable_args_ ~state (defs : (_,_,<eqn:[`Single];..>) Stmt.rec_defs) =
    let ids =
      Sequence.of_list defs
      |> Sequence.map (fun def -> def.Stmt.rec_defined.Stmt.defined_head)
      |> ID.Set.of_seq
    in
    (* traverse term, finding calls to other definitions *)
    let cg = CallGraph.create () in
    (* set of IDs being explored *)
    let explored = ID.Tbl.create 8 in
    (* explore the graph of calls in [f_id args] *)
    let rec aux f_id args t = match T.repr t with
      | TI.App (g, l) ->
          begin match T.repr g with
            | TI.Const g_id when ID.Set.mem g_id ids ->
                if ID.equal f_id g_id
                then record_self_call f_id args l
                else record_call f_id args g_id l
            | _ -> aux' f_id args t
          end
      | _ -> aux' f_id args t
    (* generic traversal *)
    and aux' f_id args t =
      U.iter () t ~bind:(fun () _ -> ()) ~f:(fun () t -> aux f_id args t)
    (* [f args1] calls itself as [f args2] in its body.
       preconditions: args1 is only variables *)
    and record_self_call f_id args1 args2 =
      List.iteri
        (fun i a2 ->
           let v = args1.(i) in
           match T.repr a2 with
             | TI.Var v' when Var.equal v v' -> () (* ok! *)
             | _ ->
                 (* if [a2] depends on some of the input variables [args1],
                    then it potentially changes at every recursive step
                    and cannot be specialized.
                     XXX the "depends" is currently too difficult to track,
                      because of local bindings (let, match), so we play it
                      safe and ask for [a2] to be closed. *)
                 if not (U.is_closed a2)
                 then CallGraph.add_nonidentical cg f_id i)
        args2
    (* [f f_args] calls [g g_args] in its body, where [g]
       belongs to the [defs] too. See how to update [cg] *)
    and record_call f_id f_args g_id g_args =
      assert (not (ID.equal f_id g_id));
      List.iteri
        (fun j arg' -> match T.repr arg' with
           | TI.Var v' ->
               (* register call in graph *)
               begin match
                   CCArray.find_idx
                     (fun v -> Var.equal v v')
                     f_args
                 with
                   | None ->
                       () (* [arg'] is not a parameter of [f] *)
                   | Some (i,_) ->
                       (* [i]-th argument of [f] is the same
                          as [j]-th argument of [g]. Now, if
                          [f=g] but [i<>j], it means we could only
                          specialize if arguments [i] and [j] are the
                          same, which is too complicated. Therefore
                          we require [f<>g or i=j], otherwise
                          [i]-th argument of [f] is blocked *)
                       CallGraph.add_call cg f_id i g_id j
               end;
           | _ -> ()
        )
        g_args;
      (* explore [g_id] if [g != f] and [g] not already explored *)
      if not (ID.equal f_id g_id) then (
        let def' = match Stmt.find_rec_def ~defs g_id with
          | None -> assert false
          | Some d -> d
        in
        if not (ID.Tbl.mem explored g_id) then (
          ID.Tbl.add explored g_id ();
          ignore (aux_def g_id def');
        )
      );
      ()
    (* process an equation *)
    and aux_def f_id def = match def.Stmt.rec_eqns with
      | Stmt.Eqn_single (vars, rhs) ->
          let args = Array.of_list vars in
          aux f_id args rhs;
          Array.length args
    in
    (* process each definition *)
    List.iter
      (fun def ->
         let id = def.Stmt.rec_defined.Stmt.defined_head in
         let n = aux_def id def in
         (* now find which arguments can be specialized, and
            register that in [state].
            An argument can be specialized iff, in [cg], it cannot
            reach [Non_identical] *)
         let bv =
           Array.init n
             (fun i ->
                not (CallGraph.can_reach_nonidentical cg (CallGraph.Arg(id,i))))
         in
         ID.Tbl.replace state.specializable_args id bv;
         Utils.debugf ~section 3 "@[<2>can specialize `@[%a : %a@]` on:@ @[%a@]@]"
           (fun k->
              let ty = def.Stmt.rec_defined.Stmt.defined_ty in
              k ID.print id P.print ty CCFormat.(array bool) bv);
      )
      defs;
    Utils.debugf ~section 5 "@[<2>call graph: @[%a@]@]" (fun k->k CallGraph.print cg);
    ()

  let free_vars_t t = U.to_seq_free_vars t |> VarSet.of_seq

  (* can [i]-th argument of [f] be specialized? *)
  let can_specialize_ ~state f i =
    try
      let bv = ID.Tbl.find state.specializable_args f in
      bv.(i)
    with Not_found -> false

  (* argument [a : ty] is good for specialization? *)
  let heuristic_should_specialize_arg a ty =
    (* is [ty] a function type? *)
    let is_fun_ty ty =
      let _, ty_args, _ = U.ty_unfold ty in
      List.length ty_args > 0
    and is_bool_const_ t = match T.repr t with
      | TI.Builtin `True
      | TI.Builtin `False -> true
      | _ -> false
    in
    is_fun_ty ty || is_bool_const_ a

  (* shall we specialize the application of [f : ty] to [l], and on which
      subset of [l]? *)
  let should_specialize ~state f ty l =
    (* apply to type arguments *)
    let info = Env.find_exn ~env:(state.get_env()) f in
    match Env.def info with
      | Env.Fun_def (defs, def, _) ->
          (* only inline defined functions, not constructors or axiomatized symbols *)
          let _, ty_args, ty_ret = U.ty_unfold ty in
          (* find the subset of arguments on which to specialize *)
          let spec_args, (other_args, ty_other_args) =
            let ty_args = Array.of_list ty_args in
            l
            |> List.mapi
              (fun i arg ->
                 assert (i<Array.length ty_args);
                 let ty = ty_args.(i) in
                 (* can we specialize on [arg], and is it interesting? *)
                 if can_specialize_ ~state f i && heuristic_should_specialize_arg arg ty
                 then `Left (i, arg) else `Right (arg,ty))
            |> CCList.partition_map CCFun.id
            |> (fun (a,b) -> Arg.make a, List.split b)
          in
          if Arg.is_empty spec_args
          then `No
          else (
            (* type of specialized function *)
            let new_ty = U.ty_arrow_l ty_other_args ty_ret in
            `Yes (spec_args, other_args, def, defs, new_ty)
          )
      | _ -> `No

  let bind_var_ subst v =
    let v' = Var.fresh_copy v in
    let subst = Var.Subst.add ~subst v v' in
    subst, v'

  (* traverse [t] and try and specialize functions at every relevant
     call site *)
  let rec specialize_term ~state ~depth subst t =
    match T.repr t with
    | TI.Var v -> U.var (Var.Subst.find_exn ~subst v)
    | TI.App (f,l) ->
        let l' = specialize_term_l ~state ~depth subst l in
        begin match T.repr f with
        | TI.Const f_id ->
            let info = Env.find_exn ~env:(state.get_env ()) f_id in
            let ty = info.Env.ty in
            if Env.is_fun info
            then match should_specialize ~state f_id ty l' with
              | `No -> U.app f l'
              | `Yes (spec_args, other_args, def, _defs, ty) ->
                  (* [spec_args] is a subset of [l'] on which we are going to
                     specialize [f].
                     [f] is defined by [def] in the mutual block [defs].
                     [other_args] are the remaining arguments *)
                  Utils.debugf ~section 5 "@[<2>specialize `@[%a@]`@ on @[%a@]@]"
                    (fun k->k P.print t Arg.print spec_args);
                  let nf = get_new_fun ~state ~depth f_id def ty spec_args in
                  state.fun_ ~depth f_id spec_args;
                  U.app (U.const nf.nf_id) other_args
            else
              U.app f l'
        | _ ->
            U.app (specialize_term ~state ~depth subst f) l'
        end
    | TI.TyBuiltin _
    | TI.Const _
    | TI.Bind _
    | TI.Let _
    | TI.Builtin _
    | TI.Match _
    | TI.TyArrow _ -> specialize_term' ~state ~depth subst t
    | TI.TyMeta _ -> assert false
  and specialize_term_l ~state ~depth subst l =
    List.map (specialize_term ~state ~depth subst) l
  and specialize_term' ~state ~depth subst t =
    U.map subst t ~bind:bind_var_ ~f:(specialize_term ~state ~depth)

  (* TODO: nothing? *)
  and specialize_ty ~state:_ ~depth:_ ty = ty

  (* TODO: find/store the new ID for [d.head args] *)
  and specialize_defined ~state d args = assert false

  (* TODO:
    - to specialize a definition for a tuple of arguments, bind those arguments
      and compute SNF of body (no def expansion, only local β reductions)
      so as to inline
  *)

  (* find or create a new function for [f args]
      @param ty the type of the new function *)
  and get_new_fun ~state ~depth f def ty args =
    (* see whether the function is already specialized on those parameters *)
    let l = try ID.Tbl.find state.new_funs f with Not_found -> [] in
    let in_cache =
      CCList.find_map
        (fun (args',fun_) -> if Arg.equal args args' then Some fun_ else None)
        l
    in
    match in_cache with
    | Some f -> f
    | None ->
        (* introduce new function *)
        let name = ID.make
          (Printf.sprintf "%s_spec_%d" (ID.to_string_slug f) state.count) in
        (* TODO: compute new function *)
        let nf = assert false in
        ID.Tbl.replace state.new_funs f ((args,nf) :: l);
        state.fun_ ~depth:(depth+1) f args;
        nf

  (* specialize equations w.r.t. the given set of arguments (with their position) *)
  let specialize_eqns
  : type i a. state:i state -> depth:int -> ID.t ->
    (term,term,a) Stmt.equations -> Arg.t -> (term,term,a) Stmt.equations
  = fun ~state ~depth id eqns arg ->
    Utils.debugf ~section 2 "@[<2>specialize@ `@[%a@]`@ on @[%a@]@]"
      (fun k->k (PStmt.print_eqns id) eqns Arg.print arg);
    match eqns with
    | Stmt.Eqn_single (vars, rhs) ->
        (* TODO: filter vars by index *)
        assert false

      (* FIXME
        state.count <- state.count + 1;
        let defined = {Stmt.defined_head=name; defined_ty=ty; } in
        (* make a new definition *)
        let eqns = specialize_eqns ~state ~depth f def.Stmt.rec_eqns args in
        let def' = { def with Stmt.
          rec_defined=defined;
          rec_vars=[]; (* monomorphic *)
          rec_eqns=eqns;
        } in
        (* save function *)
        ID.Tbl.replace state.new_funs f ((args,def') :: l);
        state.fun_ ~depth:(depth+1) f args;
        Utils.debugf ~section 4 "specialize `%a` as `%a` on `@[%a@]`"
          (fun k ->k ID.print_name f ID.print_name name Arg.print args);
        def'
         *)

  let conf = {Traversal.
    direct_tydef=true;
    direct_spec=false;
    direct_copy=true;
    direct_mutual_types=true;
  }

  (* recursive traversal of the statement graph *)
  module Trav = Traversal.Make(T)(Arg)

  class ['c] traverse ?size ?depth_limit () = object (self)
    inherit [inv, inv, 'c] Trav.traverse ~conf ?size ?depth_limit ()

    val st : _ state = create_state()

    method setup =
      st.fun_ <- self#do_statements_for_id;
      st.get_env <- (fun () -> self#env);
      ()

    method do_term ~depth t =
      specialize_term ~state:st ~depth Var.Subst.empty t

    (* specialize mutual recursive definitions *)
    method do_def ~depth def arg =
      Utils.debugf ~section 5 "@[<2>specialize def `@[%a@]`@ on `@[%a@]`@]"
        (fun k->k ID.print def.Stmt.rec_defined.Stmt.defined_head Arg.print arg);
      let id = def.Stmt.rec_defined.Stmt.defined_head in
      let eqns = specialize_eqns ~state:st ~depth id def.Stmt.rec_eqns arg in
      (* new (specialized) case *)
      let rec_defined = specialize_defined ~state:st def.Stmt.rec_defined arg in
      let def' = {Stmt.
        rec_kind=def.Stmt.rec_kind;
        rec_vars=[];
        rec_defined;
        rec_eqns=eqns;
      } in
      [def']

    method do_pred ~depth _ _ def arg =
      Utils.debugf ~section 5 "@[<2>specialize pred %a on @[%a@]@]"
        (fun k->k ID.print def.Stmt.pred_defined.Stmt.defined_head Arg.print arg);
      let clauses = assert false
      (* FIXME
        List.map
          (Stmt.map_clause
          ~term:(mono_term ~state:st ~local_state)
          ~ty:(mono_term ~state:st ~local_state))
        def.Stmt.pred_clauses
         *)
      in
      (* new (specialized) case *)
      let pred_defined = specialize_defined ~state:st def.Stmt.pred_defined arg in
      let def' = {Stmt.
        pred_tyvars=[];
        pred_defined;
        pred_clauses=clauses;
      } in
      [def']

    (* declare a symbol that is axiomatized *)
    method decl_sym ~attrs id tup =
      if not (self#has_declared id tup) then (
        let env_info = Env.find_exn ~env:self#env id in
        (* declare specialized type *)
        let new_id = assert false in
        let new_ty = assert false in
        (* FIXME
        let new_id = match Arg.mangled tup with
          | None -> id
          | Some x -> x
        in
        let ty = U.ty_apply env_info.Env.ty (Arg.args tup) in
        let new_ty = specialize_ty ~state:st ~depth:0 ty in
           *)
        self#declare_sym ~attrs id tup ~as_:new_id ~ty:new_ty
      )

    (* specialize specification *)
    method do_spec ~depth ~loc id spec tup =
      Utils.debugf ~section 5 "@[<2>specialize spec for %a@ on @[%a@]@]"
        (fun k->k ID.print id Arg.print tup);
      assert false
      (* FIXME
      assert (ArgTuple.length tup = List.length spec.Stmt.spec_vars);
      if not (self#has_processed id tup) then (
        (* flag every symbol as specialized. We can use [tup] for every
           specified symbol, as they all share the same set of type variables. *)
        let subst = match_spec ~spec tup in
        List.iter
          (fun d ->
            let id' = d.Stmt.defined_head in
            let _, mangled = mangle_ ~state:st id' (ArgTuple.m_args tup) in
            let tup' = ArgTuple.make
              ~mangled
              ~args:(ArgTuple.args tup)
              ~m_args:(ArgTuple.m_args tup) in
            Utils.debugf ~section 4 "@[<2>specialization of `@[<2>%a@ %a@]` is done@]"
              (fun k -> k ID.print id' ArgTuple.print tup');
            self#done_processing id' tup';
          )
          spec.Stmt.spec_defined;
        (* convert axioms and defined terms *)
        let defined = List.map
          (fun d -> mono_defined ~state:st ~local_state:{depth; subst;} d tup)
          spec.Stmt.spec_defined
        and axioms = List.map
          (fun ax -> mono_term ~state:st ~local_state:{depth; subst; } ax)
          spec.Stmt.spec_axioms
        in
        let st' = Stmt.axiom_spec ~info:{Stmt.loc; name=None}
          {Stmt.spec_axioms=axioms; spec_defined=defined; spec_vars=[]; }
        in
        self#push_res st';
      );
      ()
         *)

    (* XXX direct translation of types/copy types/defs should be
       ok, because specializing doesn't remove the need for a given
       type — all the types needed before are still useful (and kept
       identically) in the output. *)

    (* direct translation *)
    method do_mutual_types ~depth: _ _ = assert false

    (* direct translation *)
    method do_copy ~depth:_ ~loc:_ _ _ = assert false

    (* direct translation *)
    method do_ty_def ?loc:_ ~attrs:_ _ _ ~ty:_ _ = assert false
  end

  let specialize_problem pb =
    let state = create_state() in
    let trav = new traverse () in
    trav#setup;
    (* first, compute specializable arguments *)
    Problem.iter_statements pb
      ~f:(fun stmt -> match Stmt.view stmt with
        | Stmt.Axiom (Stmt.Axiom_rec defs) ->
            compute_specializable_args_ ~state defs
        | Stmt.Axiom (Stmt.Axiom_spec _) ->
            assert false (* TODO!!! *)
        | _ -> ());
    (* then, transform *)
    Problem.iter_statements pb ~f:trav#do_stmt;
    (* TODO: also add extensionality axioms for new functions *)
    let pb' =
      trav#output
      |> CCVector.freeze
      |> Problem.make ~meta:(Problem.metadata pb)  in
    pb', state.decode

  (* traverse the term and use reverse table to replace specialized
     functions by their definition *)
  let decode_term _state _t = _t (* TODO *)

  let pipe_with ~decode ~print ~check =
    let on_encoded =
      Utils.singleton_if print () ~f:(fun () ->
        let module P = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after specialization@}: %a@]@." P.print)
      @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.check_problem ?env:None)
    in
    Transform.make1
      ~name
      ~on_encoded
      ~encode:(fun pb ->
        let pb, decode = specialize_problem pb in
        pb, decode
      )
      ~decode:(fun state x ->
        decode (decode_term state) x
      )
      ()

  let pipe ~print ~check =
    let decode decode_term =
      Model.map ~term:decode_term ~ty:decode_term
    in
    pipe_with ~decode ~print ~check
end

