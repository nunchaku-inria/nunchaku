
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Specialization} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module Subst = Var.Subst
module T = TI.Default
module P = T.P
module U = T.U
module PStmt = Stmt.Print(P)(P)
module Red = Reduce.Make(T)
module VarSet = U.VarSet
module AT = AnalyzeType.Make(T)

type term = T.t
type ty = T.t

let name = "specialize"
let fpf = Format.fprintf

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "in specialization: " ^ msg)
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

  (*
  (* view [t] as a graph *)
  let as_graph g =
    let children n =
      try IDIntTbl.find g n |> Sequence.of_list
      with Not_found -> Sequence.empty
    in
    CCGraph.make_tuple children
     *)

  let print out g =
    let pp_node out = function
      | Non_identical -> CCFormat.string out "<non-identical>"
      | Arg (id,n) -> fpf out "arg(%a,%d)" ID.print id n
    in
    let pp_pair out (n,c) =
      fpf out "@[<2>%a ->@ [@[%a@]]@]"
        pp_node n (CCFormat.list ~start:"" ~stop:"" pp_node) c.cell_children
    in
    fpf out "@[<hv>@[<hv2>graph {@,@[<v>%a@]@]@,}@]"
      (CCFormat.seq ~start:"" ~stop:"" pp_pair) (IDIntTbl.to_seq g)
end

(* Specialization of a function is parametrized by a set of (fixed)
   arguments of the function *)
module Arg : sig
  include Traversal.ARG
  val empty : t
  val is_empty : t -> bool
  val length : t -> int
  val mem : int -> t -> bool
  val get : int -> t -> T.t
  val to_list : t -> (int * T.t) list
  val vars : t -> ty Var.t list
  val make : (int * T.t) list -> t
end = struct
  type t = {
    terms: (int * T.t) list; (* sorted *)
    vars: ty Var.t list;
  }

  let empty = {terms=[]; vars=[]}
  let is_empty = function {terms=[];_} -> true | _ -> false
  let length a = List.length a.terms
  let make l =
    let terms = List.sort (fun (i,_)(j,_) -> Pervasives.compare i j) l in
    let vars =
      Sequence.of_list l
      |> Sequence.map snd
      |> Sequence.flat_map (U.to_seq_free_vars ?bound:None)
      |> VarSet.of_seq |> VarSet.to_list
    in
    {terms; vars}
  let mem i a = List.mem_assoc i a.terms
  let get i a = List.assoc i a.terms
  let to_list a = a.terms
  let vars a = a.vars

  let rec equal_l l1 l2 = match l1, l2 with
    | [], [] -> true
    | [], _ | _, [] -> false
    | (i1,t1) :: l1', (i2,t2) :: l2' ->
      i1 = i2 && U.equal t1 t2 && equal_l l1' l2'

  (* NOTE: since equality is up to variable renaming, we use
     the {!U.hash_fun_alpha_eq} hash function which is compatible with alpha-renaming *)

  let equal a b = equal_l a.terms b.terms

  let hash_fun a h = CCHash.(list (pair int U.hash_fun_alpha_eq)) a.terms h
  let hash = CCHash.apply hash_fun

  let print out a =
    let pp_pair out (i,t) = fpf out "@[%d -> %a@]" i P.print t in
    fpf out "[@[<hv>%a@]]" (CCFormat.list ~start:"" ~stop:"" pp_pair) a.terms
  let section = section
  let fail = errorf
end

type new_fun = {
  nf_id: ID.t;  (* name of new function *)
  nf_ty: ty;
  nf_specialized_from: ID.t; (* source *)
}

type new_funs = {
  nfs_needs_congruence: bool;
  (* if [true], the function needs some congruence axioms *)
  nfs_instances: [ `New of Arg.t * new_fun | `Same] list;
  (* list of instances *)
}

(* decoding state for one function *)
type decode_state_fun = {
  dsf_spec_of: ID.t; (* what was the original function, before spec? *)
  dsf_ty_of: ty; (* type of original function *)
  dsf_arg: Arg.t; (* specialization tuple *)
}

type decode_state = decode_state_fun ID.Tbl.t

type state = {
  specializable_args : bool array ID.Tbl.t;
  (* function -> list of argument positions that can be specialized *)
  new_funs: new_funs ID.Tbl.t;
  (* maps [f] to a list of [`New (args_i, f')], where each [f'] is
      a specialization of [f] on [args_i],
      or to [`Same], meaning [f] is also used as-is.
      [f'] has a type that should allow it to be applied to [map snd args_i] *)
  mutable count: int;
  (* used for new names *)
  decode: decode_state;
  (* used for decoding new symbols *)
  new_decls: (term, ty) Stmt.t CCVector.vector;
  (* vector of new declarations *)
  at_cache: AT.cache;
  (* for computing cardinalities *)
}

let create_state () : state = {
  specializable_args=ID.Tbl.create 32;
  new_funs=ID.Tbl.create 32;
  count=0;
  decode=ID.Tbl.create 32;
  new_decls=CCVector.create();
  at_cache=AT.create_cache ();
}

(* recursive traversal of the statement graph *)
module Trav = Traversal.Make(T)(Arg)(struct type t = state end)

(** {6 Analysis of Call Graph}

    We need to know which arguments of a function are eligible for
    specialization: those that will not require to unroll the function
    over each recursive call. In other words, those are the arguments
    that are given "as is" to the recursive calls.
    Examples:
    - [f] in [List.map f l]
    - [R] in [transitive_closure R x y] *)

(* state used for analysing the call graph of a block of mutual definitions *)
type 'a call_graph_analyze_state = {
  cga_graph: CallGraph.t;
  cga_env: (term,ty) Env.t;
  cga_ids: ID.Set.t; (* IDs defined in the same block of mutual definitions *)
  cga_explored: unit ID.Tbl.t; (* explored nodes *)
}

let fresh_var_cg = Var.make_gen ~names:"v_cg_%d"

(* explore the graph of calls in [f_id args] *)
let rec record_calls_term cga f_id args t = match T.repr t with
  | TI.App (g, l) ->
    begin match T.repr g with
      | TI.Const g_id when ID.Set.mem g_id cga.cga_ids ->
        if ID.equal f_id g_id
        then record_self_call cga f_id args l
        else record_call cga f_id args g_id l
      | _ -> record_calls_term' cga f_id args t
    end
  | _ -> record_calls_term' cga f_id args t
(* generic traversal *)
and record_calls_term' cga id args t =
  U.iter () t ~bind:(fun () _ -> ())
    ~f:(fun () t -> record_calls_term cga id args t)

(* [f f_args] calls itself as [f args2] in its body. *)
and record_self_call cga f_id f_args args2 =
  List.iteri
    (fun i a2 ->
       let v = f_args.(i) in
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
           then CallGraph.add_nonidentical cga.cga_graph f_id i)
    args2

(* [f f_args] calls [g g_args] in its body, where [g]
   belongs to the [defs] too. See how to update [cg] *)
and record_call cga f_id f_args g_id g_args =
  assert (not (ID.equal f_id g_id));
  List.iteri
    (fun j arg' -> match T.repr arg' with
       | TI.Var v' ->
         (* register call in graph *)
         begin match
             CCArray.find_idx (fun v -> Var.equal v v') f_args
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
               CallGraph.add_call cga.cga_graph f_id i g_id j
         end;
       | _ -> ()
    )
    g_args;
  (* explore [g_id] if [g != f] and [g] not already explored *)
  if not (ID.equal f_id g_id) then (
    if not (ID.Tbl.mem cga.cga_explored g_id) then (
      ID.Tbl.add cga.cga_explored g_id ();
      let info = Env.find_exn ~env:cga.cga_env g_id in
      match Env.def info with
        | Env.Fun_def (_,d,_) -> ignore (record_calls_def cga g_id d)
        | Env.Pred (_,_,p,_,_) -> ignore (record_calls_pred cga g_id p)
        | _ -> assert false
    )
  );
  ()

(* process an equation *)
and record_calls_def cga id def = match def.Stmt.rec_eqns with
  | Stmt.Eqn_single (vars, rhs) ->
    let args = Array.of_list vars in
    record_calls_term cga id args rhs;
    Array.length args
  | Stmt.Eqn_app _
  | Stmt.Eqn_nested _ -> assert false

(* process one clause of a (co)inductive predicate *)
and record_calls_clause cga id (c:(_,_) Stmt.pred_clause) =
  match T.repr c.Stmt.clause_concl with
    | TI.Const _ -> ()  (* no recursion is possible *)
    | TI.App (f, l) ->
      begin match T.repr f with
        | TI.Const f_id ->
          assert (ID.equal id f_id);
          (* variables already met *)
          let vars_seen = ref VarSet.empty in
          (* check which arguments are "unique" variables (those
             which are not are directly flagged as "non-identical"
             and mapped to a dummy var) *)
          let args =
            Array.of_list l
            |> Array.mapi
              (fun i t -> match T.repr t with
                 | TI.Var v when not (VarSet.mem v !vars_seen) ->
                   vars_seen := VarSet.add v !vars_seen;
                   v
                 | _ ->
                   (* recursion impossible, not a variable *)
                   CallGraph.add_nonidentical cga.cga_graph id i;
                   let ty = U.ty_exn ~env:cga.cga_env t in
                   fresh_var_cg ty)
          in
          (* if present, also check the clause guard *)
          CCOpt.iter (record_calls_term cga id args) c.Stmt.clause_guard
        | _ -> assert false (* ill formed *)
      end
    | _ -> assert false (* ill-formed *)

(* process a (co)inductive predicate) *)
and record_calls_pred cga id pred =
  List.iter
    (record_calls_clause cga id)
    pred.Stmt.pred_clauses;
  let _, ty_args, _ =
    pred |> Stmt.defined_of_pred |> Stmt.ty_of_defined |> U.ty_unfold in
  List.length ty_args

let mk_cga_state ~env ids : _ call_graph_analyze_state = {
  cga_graph=CallGraph.create();
  cga_explored=ID.Tbl.create 8;
  cga_ids=ids;
  cga_env=env;
}

(* [id] has [n] arguments, find which arguments of [id] can be specialized.
   An argument can be specialized iff, in [cg], it cannot reach
   [Non_identical] *)
let bv_of_callgraph cg id n =
  Array.init n
    (fun i ->
       not
         (CallGraph.can_reach_nonidentical cg
            (CallGraph.Arg(id,i))))

(* compute the set of specializable arguments in each function of [defs] *)
let compute_specializable_args_def ~self (defs : (_,_) Stmt.rec_defs) =
  let state = Trav.state self in
  let ids =
    Stmt.defined_of_recs defs
    |> Sequence.map Stmt.id_of_defined
    |> ID.Set.of_seq
  in
  let cga = mk_cga_state ~env:(Trav.env self) ids in
  (* process each definition *)
  List.iter
    (fun def ->
       let id = def.Stmt.rec_defined.Stmt.defined_head in
       let n = record_calls_def cga id def in
       let bv = bv_of_callgraph cga.cga_graph id n in
       ID.Tbl.replace state.specializable_args id bv;
       Utils.debugf ~section 3 "@[<2>can specialize `@[%a : %a@]` on:@ @[%a@]@]"
         (fun k->
            let ty = def.Stmt.rec_defined.Stmt.defined_ty in
            k ID.print_full id P.print ty CCFormat.(array bool) bv);
    )
    defs;
  Utils.debugf ~section 5 "@[<2>call graph: @[%a@]@]"
    (fun k->k CallGraph.print cga.cga_graph);
  ()

(* similar to {!compute_specializable_args_def} *)
let compute_specializable_args_pred ~self (preds : (_,_) Stmt.pred_def list) =
  let state = Trav.state self in
  let ids =
    Stmt.defined_of_preds preds
    |> Sequence.map Stmt.id_of_defined
    |> ID.Set.of_seq
  in
  let cga = mk_cga_state ~env:(Trav.env self) ids in
  (* process each definition *)
  List.iter
    (fun pred ->
       let id = pred.Stmt.pred_defined.Stmt.defined_head in
       let n = record_calls_pred cga id pred in
       (* now find which arguments can be specialized, and
          register that in [state]. *)
       let bv = bv_of_callgraph cga.cga_graph id n in
       ID.Tbl.replace state.specializable_args id bv;
       Utils.debugf ~section 3 "@[<2>can specialize `@[%a : %a@]` on:@ @[%a@]@]"
         (fun k->
            let ty = pred.Stmt.pred_defined.Stmt.defined_ty in
            k ID.print_full id P.print ty CCFormat.(array bool) bv);
    )
    preds;
  Utils.debugf ~section 5 "@[<2>call graph: @[%a@]@]"
    (fun k->k CallGraph.print cga.cga_graph);
  ()

(* can [i]-th argument of [f] be specialized? *)
let can_specialize_ ~state f i =
  try
    let bv = ID.Tbl.find state.specializable_args f in
    bv.(i)
  with Not_found ->
    errorf "could not find specializable_args[%a]" ID.print_full f

(* before processing a statement, analyse the call graph *)
let analyze_cg_st ~self stmt =
  match Stmt.view stmt with
    | Stmt.Axiom (Stmt.Axiom_rec defs) ->
      compute_specializable_args_def ~self defs
    | Stmt.Pred (_,_,preds) ->
      compute_specializable_args_pred ~self preds
    | _ -> ()

(** {6 Specialization}

    The part where terms are traversed, and function calls specialized
    (or not), according to heuristics and call graphs computed above. *)

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

type specialization_params = {
  spec_args: Arg.t;
  (* the definition is specialized w.r.t those terms *)
  other_args: term list;
  (* remaining arguments that will also be parameters to the specialized
     version of the function *)
  new_ty: ty;
  (* type of the new function *)
}

type specialization_decision =
  | Do_not_specialize
  | Do_specialize of specialization_params

(* maximum size of the cardinal of a closure variable's type. *)
let max_closure_var_type_card = 10 (* FUDGE *)

(* TODO: if we have a "total" annotation on functions (including [unique_unsafe])
   or Coq functions, we can avoid generating congruence axioms for those
   functions.
*)

(* is the function deterministic?
   this should be a safe approximation, that is, only return [true] if we
   are {b sure} that the function is. When in doubt, return [false] *)
let fun_is_deterministic ~self:_ (_f:ID.t): bool =
  false (* TODO *)

(* do NOT specialize if at least one closure argument
   has a type which is too large (see {!max_closure_var_type_card})
   or infinite.
   The reason is that closure variables are universally quantified
   upon, and infinite quantifiers are bad for us *)
let closure_variable_has_small_ty ~self (v:ty Var.t): bool =
  let state = Trav.state self in
  let card_ty =
    AT.cardinality_ty ~cache:state.at_cache (Trav.env self) (Var.ty v)
  in
  let module C = Cardinality in
  begin match card_ty with
    | C.Exact n | C.QuasiFiniteGEQ n ->
      C.Z.compare n (C.Z.of_int max_closure_var_type_card) <= 0
    | C.Infinite | C.Unknown -> false
  end

(* check whether all free variables of [t]
   satisfy {!closure_variable_has_small_ty} *)
let arg_has_small_ty_closure_vars ~self t: bool =
  VarSet.for_all (closure_variable_has_small_ty ~self) (U.free_vars t)

(* shall we specialize the application of [f : ty] to [l], and on which
    subset of [l]? *)
let decide_if_specialize ~self f ty l : specialization_decision =
  (* apply to type arguments *)
  let info = Env.find_exn ~env:(Trav.env self) f in
  let is_deterministic = fun_is_deterministic ~self f in
  match Env.def info with
    | Env.Fun_def _ ->
      (* only inline defined functions, not constructors or axiomatized symbols *)
      let _, ty_args_l, ty_ret = U.ty_unfold ty in
      let ty_args = Array.of_list ty_args_l in
      (* find the subset of arguments on which to specialize *)
      let spec_args, other_args =
        l
        |> List.mapi
          (fun i arg ->
             assert (i<Array.length ty_args);
             let ty = ty_args.(i) in
             (* can we specialize on [arg], and is it interesting? *)
             if can_specialize_ ~state:(Trav.state self) f i
             && not (U.is_var arg)
             && heuristic_should_specialize_arg arg ty
             (* will we have to pay specialization with evil congruence axioms? *)
             && (is_deterministic || arg_has_small_ty_closure_vars ~self arg)
             then `Specialize (i, arg)
             else `Keep arg)
        |> CCList.partition_map
          (function `Specialize x -> `Left x | `Keep y -> `Right y)
        |> (fun (a,b) -> Arg.make a, b)
      in
      if Arg.is_empty spec_args
      then Do_not_specialize
      else (
        (* type of specialized function. We cannot use [other_args]
           because [f] might be partially applied. *)
        let ty_remaining_args =
          Utils.filteri (fun i _ -> not (Arg.mem i spec_args)) ty_args_l
        (* new arguments: types of free variables of [spec_args] *)
        and ty_new_args = Arg.vars spec_args |> List.map Var.ty in
        let new_ty = U.ty_arrow_l (ty_new_args @ ty_remaining_args) ty_ret in
        Do_specialize {
          spec_args;
          other_args;
          new_ty;
        }
      )
    | _ -> Do_not_specialize

let find_new_fun ~state f args =
  (* see whether the function is already specialized on those parameters *)
  match ID.Tbl.get state.new_funs f with
    | None -> None
    | Some nfs ->
      CCList.find_map
        (function
          | `Same -> None
          | `New (args',fun_) -> if Arg.equal args args' then Some fun_ else None)
        nfs.nfs_instances

let find_new_fun_exn ~state f args =
  match find_new_fun ~state f args with
    | Some res -> res
    | None ->
      errorf "@[<2>could not find new definition for %a on @[%a@]@]"
        ID.print f Arg.print args

let add_instance ~self f i: unit =
  let state = Trav.state self in
  match ID.Tbl.get state.new_funs f with
    | Some nfs ->
      let nfs_instances = i :: nfs.nfs_instances in
      ID.Tbl.replace state.new_funs f {nfs with nfs_instances}
    | None ->
      let nfs = {
        nfs_instances=[i];
        nfs_needs_congruence=not (fun_is_deterministic ~self f);
      } in
      ID.Tbl.add state.new_funs f nfs

(* require [f] to be defined in the output, but without specializing
   it on any of its arguments *)
let require_without_specializing ~self ~depth f =
  Trav.call_dep self ~depth f Arg.empty;
  let state = Trav.state self in
  (* remember that [f] is used without specialization *)
  let l = try (ID.Tbl.find state.new_funs f).nfs_instances with Not_found -> [] in
  if not (List.mem `Same l) then (
    add_instance ~self f `Same;
  );
  ()

(* traverse [t] and try and specialize functions at every relevant
   call site
    @param subst used to rename variables and, possibly, replace
    specialized variables by the corresponding constant *)
let rec specialize_term ~self ~depth subst t =
  match T.repr t with
    | TI.Var v -> Var.Subst.find_exn ~subst v
    | TI.Const f_id ->
      require_without_specializing ~self ~depth f_id;
      t
    | TI.App (f,l) ->
      let l' = specialize_term_l ~self ~depth subst l in
      begin match T.repr f with
        | TI.Const f_id ->
          let info = Env.find_exn ~env:(Trav.env self) f_id in
          let ty = info.Env.ty in
          if Env.is_rec info
          then match decide_if_specialize ~self f_id ty l' with
            | Do_not_specialize ->
              (* still require [f]'s definition *)
              require_without_specializing ~self ~depth f_id;
              U.app f l'
            | Do_specialize {spec_args; other_args; new_ty} ->
              (* [spec_args] is a subset of [l'] on which we are going to
                   specialize [f].
                 [other_args] are the remaining arguments,
                 [new_ty] is the type of the specialized version of [f] *)
              Utils.debugf ~section 5
                "@[<2>@{<Cyan>specialize@} `@[%a@]`@ on @[%a@]@ with new type `@[%a@]`@]"
                (fun k->k P.print t Arg.print spec_args P.print new_ty);
              let nf = get_new_fun ~self ~depth f_id ~old_ty:ty ~new_ty spec_args in
              (* ensure that [nf] is defined *)
              Trav.call_dep self ~depth f_id spec_args;
              (* apply newly specialized function to both the captured
                 variables [closure_args] and the non-specialized arguments. *)
              let closure_args = List.map U.var (Arg.vars spec_args) in
              U.app_const nf.nf_id (closure_args @ other_args)
          else (
            Trav.call_dep self ~depth f_id Arg.empty;
            U.app f l'
          )
        | _ ->
          U.app (specialize_term ~self ~depth subst f) l'
      end
    | TI.TyBuiltin _
    | TI.Bind _
    | TI.Let _
    | TI.Builtin _
    | TI.Match _
    | TI.TyArrow _ -> specialize_term' ~self ~depth subst t
    | TI.TyMeta _ -> assert false
and specialize_term_l ~self ~depth subst l =
  List.map (specialize_term ~self ~depth subst) l
and specialize_term' ~self ~depth subst t =
  U.map subst t ~bind:U.rename_var ~f:(specialize_term ~self ~depth)

(* find or create a new function for [f args]
    @param new_ty the type of the new function *)
and get_new_fun ~self ~depth f ~old_ty ~new_ty args =
  let state = Trav.state self in
  match find_new_fun ~state f args with
    | Some f -> f
    | None ->
      (* introduce new function, keeping appropriate attributes *)
      let name =
        ID.make_full
          ~needs_at:(ID.needs_at f) ~pol:(ID.polarity f)
          (Printf.sprintf "%s_spec_%d" (ID.to_string_slug f) state.count) in
      let nf = {
        nf_specialized_from=f;
        nf_id=name;
        nf_ty=new_ty;
      } in
      (* add [nf] to the list of specialized versions of [f] *)
      add_instance ~self f (`New (args,nf));
      let dsf = {
        dsf_spec_of=f;
        dsf_ty_of=old_ty;
        dsf_arg=args;
      } in
      ID.Tbl.replace state.decode nf.nf_id dsf;
      Trav.call_dep self ~depth:(depth+1) f args;
      nf

let specialize_defined ~state d args =
  if Arg.is_empty args
  then d
  else
    let nf = find_new_fun_exn ~state d.Stmt.defined_head args in
    Stmt.mk_defined ~attrs:[] nf.nf_id nf.nf_ty

(* specialize equations w.r.t. the given set of arguments (with their position)
    to specialize a definition for a tuple of arguments, bind those arguments
    and compute SNF of body (no def expansion, only local β reductions)
    so as to inline *)
let specialize_eqns
  : self:Trav.t -> depth:int -> ID.t ->
  (term,term) Stmt.equations -> Arg.t -> (term,term) Stmt.equations
  = fun ~self ~depth id eqns args ->
    Utils.debugf ~section 2 "@[<2>specialize@ `@[%a@]`@ on @[%a@]@]"
      (fun k->k (PStmt.print_eqns id) eqns Arg.print args);
    let state = Trav.state self in
    match eqns with
      | Stmt.Eqn_single (vars, rhs) ->
        if Arg.is_empty args then (
          (* still need to traverse [rhs] *)
          let subst, vars = Utils.fold_map U.rename_var Subst.empty vars in
          let rhs = specialize_term ~self ~depth:(depth+1) subst rhs in
          Stmt.Eqn_single (vars, rhs)
        ) else (
          state.count <- state.count + 1;
          let subst = Subst.empty in
          (* XXX: do not rename the "closure variables"
             (i.e. the free variables in [args])
             because it induces a loop in specialization:
             in the body, we might want to specialize on the same function
             but it is a different term after renaming, so Traversal doesn't
             detect the loop. *)
          let closure_vars = Arg.vars args in
          (* bind variables whose position corresponds to a member of [args] *)
          let subst, new_vars =
            Utils.fold_mapi vars ~x:subst
              ~f:(fun i subst v ->
                (* keep [v] if its index [i] is not in [args], otherwise
                   replace it with the corresponding term [t], after
                   renaming of its free variables *)
                try
                  let t = Arg.get i args |> U.eval ~rec_:false ~subst in
                  Subst.add ~subst v t, None
                with Not_found ->
                  let v' = Var.fresh_copy v in
                  Subst.add ~subst v (U.var v'), Some v')
          in
          let new_vars = CCList.filter_map CCFun.id new_vars in
          (* specialize the body, using the given substitution;
             then reduce newly introduced β-redexes, etc. *)
          let rhs' = specialize_term ~self ~depth:(depth+1) subst rhs in
          let new_rhs = Red.snf rhs' in
          Stmt.Eqn_single (closure_vars @ new_vars, new_rhs)
        )
      | Stmt.Eqn_app _
      | Stmt.Eqn_nested _ -> assert false

let specialize_clause
  : self:Trav.t -> depth:int -> ID.t ->
  (term,term) Stmt.pred_clause -> Arg.t -> (term,term) Stmt.pred_clause
  = fun ~self ~depth id c args ->
    Utils.debugf ~section 2 "@[<2>specialize@ `@[%a@]`@ on @[%a@]@]"
      (fun k->k PStmt.print_clause c Arg.print args);
    let state = Trav.state self in
    if Arg.is_empty args then (
      (* still need to traverse the clause *)
      let subst, vars = Utils.fold_map U.rename_var Subst.empty c.Stmt.clause_vars in
      let spec_term = specialize_term ~self ~depth:(depth+1) subst in
      let clause_guard = CCOpt.map spec_term c.Stmt.clause_guard in
      let clause_concl = spec_term c.Stmt.clause_concl in
      {Stmt.clause_vars=vars; clause_guard; clause_concl}
    ) else (
      (* specialize. Since we are allowed to do it, it means that positions
         of [args] designate arguments in the clause that are variables. *)
      state.count <- state.count + 1;
      let subst = Subst.empty in
      (* variables captured in closure (do not rename, see {!specialize_eqns})  *)
      let closure_vars = Arg.vars args in
      (* bind variables corresponding to specialized positions *)
      let subst, clause_concl = match T.repr c.Stmt.clause_concl with
        | TI.App (f, l) ->
          assert (List.length l >= Arg.length args);
          assert (match T.repr f with TI.Const f_id -> ID.equal f_id id | _ -> false);
          (* now remove the specialized arguments *)
          let subst, l' =
            Utils.fold_mapi l ~x:subst
              ~f:(fun i subst arg_i ->
                try
                  let new_arg = Arg.get i args in
                  let v = match T.repr arg_i with
                    | TI.Var v -> v
                    | _ -> assert false (* should not have been allowed to specialize *)
                  in
                  Subst.add ~subst v new_arg, None
                with Not_found ->
                  (* keep argument *)
                  subst, Some arg_i)
          in
          let l' = CCList.filter_map CCFun.id l' in
          subst, U.app f (List.map U.var closure_vars @ l')
        | _ -> assert false
      in
      (* if there is a guard, specialize it and β-reduce *)
      let clause_guard =
        CCOpt.map
          (fun t ->
             let t' = specialize_term ~self ~depth:(depth+1) subst t in
             Red.snf t')
          c.Stmt.clause_guard
      in
      (* compute new set of free variables *)
      let new_vars =
        let v1 = U.free_vars clause_concl in
        CCOpt.map_or ~default:v1 (fun t -> VarSet.union (U.free_vars t) v1) clause_guard
        |> VarSet.to_list
      in
      {Stmt.clause_guard; clause_concl; clause_vars=new_vars}
    )

let dispatch = {
  Trav.

  do_term = (fun self ~depth t ->
    specialize_term ~self ~depth Subst.empty t
  );

  do_goal_or_axiom = None;

  (* specialize mutual recursive definitions *)
  do_def = (fun self ~depth def args ->
    Utils.debugf ~section 5 "@[<2>specialize def `@[%a@]`@ on `@[%a@]`@]"
      (fun k->k ID.print def.Stmt.rec_defined.Stmt.defined_head Arg.print args);
    let st = Trav.state self in
    let id = def |> Stmt.defined_of_rec |> Stmt.id_of_defined in
    let eqns = specialize_eqns ~self ~depth id def.Stmt.rec_eqns args in
    (* new (specialized) case *)
    let rec_defined = specialize_defined ~state:st def.Stmt.rec_defined args in
    let def' = {Stmt.
                 rec_ty_vars=[];
                 rec_defined;
                 rec_eqns=eqns;
               } in
    def'
  );

  (* specialize (co)inductive predicates *)
  do_pred = (fun self ~depth _wf _kind pred args ->
    Utils.debugf ~section 5 "@[<2>specialize pred `@[%a@]`@ on `@[%a@]`@]"
      (fun k->k ID.print pred.Stmt.pred_defined.Stmt.defined_head Arg.print args);
    let st = Trav.state self in
    assert (pred.Stmt.pred_tyvars=[]);
    let id = pred.Stmt.pred_defined.Stmt.defined_head in
    let clauses =
      List.map
        (fun c -> specialize_clause ~self ~depth id c args)
        pred.Stmt.pred_clauses in
    (* new (specialized) case *)
    let pred_defined = specialize_defined ~state:st pred.Stmt.pred_defined args in
    let pred' = {Stmt.
                  pred_defined;
                  pred_clauses=clauses;
                  pred_tyvars=[];
                } in
    pred'
  );

  (* should never happen, spec is fallthrough *)
  do_spec = None;

  (* XXX direct translation of types/copy types/defs should be
     ok, because specializing doesn't remove the need for a given
     type — all the types needed before are still useful (and kept
     identically) in the output. *)

  (* direct translation *)
  do_data = None;

  (* direct translation *)
  do_copy = None;

  (* direct translation *)
  do_ty_def = None;
}

(** {6 Generation of Congruence Axioms}

    If [f x y] is specialized as [f1 x ≡ f x a], and [f2 y = f b y],
    and [f] is also used unspecialized, we need to make sure that:
    - [f1 b = f2 a = f a b]
    - [f1 x = f x a]
    - [f2 y = f b y]
    this part generates the required axioms. *)

(* graph of subsumption relations between various instances of the same
   function, forming a lattice ordered by generality ("f args1 < f args2"
   iff "\exists \sigma. args2\sigma = args1") *)
module InstanceGraph = struct
  type vertex = {
    v_id: ID.t; (* name of the specialized function *)
    v_spec_of: ID.t; (* name of generic function *)
    v_spec_on: Arg.t; (* arguments on which [v_spec_of] is specialized *)
    v_args: term list; (* [v_id v_spec_on = v_spec_of v_args] *)
    v_term: term; (* [v_spec_of v_args] *)
  }

  type parent_edge = (term, ty) Subst.t * vertex
  (* edge to a parent, that is,
     [v1 -> sigma, v2] means [v_to_term v2\sigma = v_to_term v1] *)

  type t = {
    id: ID.t;
    (* function that is specialized in various ways *)
    ty_args : ty list;
    (* type parameters of [id] *)
    vertices: (vertex * parent_edge option) list;
    (* list of all args used, plus their (optional) parent *)
  }

  (* [subsumes_ v1 v2] returns [Some sigma] if [sigma v1.term = v2.term], None otherwise *)
  let subsumes_ v1 v2 = U.match_ v1.v_term v2.v_term

  (* add edges to some parent for every non-root vertex in [l] *)
  let find_parents l =
    let find_parent v =
      CCList.find_map
        (fun v' ->
           if ID.equal v.v_id v'.v_id then None
           else CCOpt.map (fun sigma -> sigma, v') (subsumes_ v' v))
        l
    in
    List.map (fun v -> v, find_parent v) l

  let app_const id l = U.app (U.const id) l

  let fresh_var = Var.make_gen ~names:"v_ig_%d"
  let fresh_var_t ty = U.var (fresh_var ty)

  (* rename variables in [t] *)
  let rename_vars l =
    let vars =
      Sequence.of_list l
      |> Sequence.flat_map (U.to_seq_free_vars ?bound:None)
      |> VarSet.of_seq
      |> VarSet.to_list in
    let vars' = List.map Var.fresh_copy vars in
    let subst = Subst.add_list ~subst:Subst.empty vars vars' in
    List.map (U.eval_renaming ~subst) l

  (* build graph from a [state.new_funs] entry corresponding to [id:ty_args -> _] *)
  let make id ty_args l =
    let vars = List.map fresh_var_t ty_args in
    let vertices =
      l
      |> List.map
        (function
          | `Same ->
            let v_args = List.map fresh_var_t ty_args in
            let v_term = app_const id v_args in
            {v_id=id; v_spec_of=id; v_spec_on=Arg.empty; v_args; v_term; }
          | `New (arg,nf) ->
            let v_args =
              List.mapi
                (fun i a ->
                   try Arg.get i arg
                   with Not_found -> a)
                vars
              |> rename_vars
            in
            let v_term = app_const nf.nf_id v_args in
            {v_id=nf.nf_id; v_spec_of=id; v_spec_on=arg; v_args; v_term}
        )
      |> find_parents
    in
    { id; ty_args; vertices; }

  let all_vertices g =
    Sequence.of_list g.vertices
    |> Sequence.map fst

  (* nodes without parents *)
  let roots g =
    Sequence.of_list g.vertices
    |> Sequence.filter_map
      (function (v,None) -> Some v | (_,Some _) -> None)

  (* nodes that have a parent *)
  let non_roots g =
    Sequence.of_list g.vertices
    |> Sequence.filter_map
      (function (_,None) -> None | (v1,Some v2) -> Some (v1,v2))

  let print out g =
    let pp_vertex out v =
      fpf out "{@[%a on %a@]}" ID.print v.v_id Arg.print v.v_spec_on in
    let pp_edge out = function
      | None -> ()
      | Some (sigma,v') ->
        fpf out " --> @[%a@] with @[%a@]" pp_vertex v' (Subst.print P.print) sigma
    in
    let pp_item out (v,e) = fpf out "@[<2>%a@,%a@]" pp_vertex v pp_edge e in
    fpf out "@[<2>instance graph for %a:@ @[<v>%a@]@]" ID.print g.id
      (CCFormat.list ~start:"" ~stop:"" pp_item) g.vertices
end

(* each vertex corresponds to a (specialized) term *)
let spec_term_of_vertex v =
  let open InstanceGraph in
  let closure_vars = Arg.vars v.v_spec_on in
  let args = Utils.filteri (fun i _ -> not (Arg.mem i v.v_spec_on)) v.v_args in
  let t = U.app_const v.v_id (List.map U.var closure_vars @ args) in
  Red.snf t

let mk_congruence_axiom v1 v2 =
  let module IG = InstanceGraph in
  assert (List.length v1.IG.v_args = List.length v2.IG.v_args);
  let eqns = List.map2 U.eq v1.IG.v_args v2.IG.v_args in
  let concl = U.eq (spec_term_of_vertex v1) (spec_term_of_vertex v2) in
  let ax = U.imply_l eqns concl in
  U.close_forall ax

(* add self-congruence axioms, if needed.
   Those axioms are relevant when a non-deterministic function is
   specialized with arguments that have closure variables.

   For instance, specializing [choice (fun x. f x y)]
   should create [choice42 y], with the axiom
   [forall y1 y2. (fun x. f x y1)=(fun x. f x y2) => choice42 y1=choice42 y2]
   (e.g. if [f] ignores its second argument)
*)
let mk_self_congruence (v:InstanceGraph.vertex): term option =
  let module IG = InstanceGraph in
  let arg = v.IG.v_spec_on in
  let vars = Arg.vars arg in
  if vars=[] then None
  else (
    let vars1 = List.mapi (fun i v -> Var.makef ~ty:(Var.ty v) "x_%d" i) vars in
    let vars2 = List.mapi (fun i v -> Var.makef ~ty:(Var.ty v) "y_%d" i) vars in
    let subst1 = Var.Subst.of_list vars1 vars in
    let subst2 = Var.Subst.of_list vars2 vars in
    let conds =
      List.map
         (fun a ->
            U.eq
              (U.eval_renaming ~subst:subst1 a)
              (U.eval_renaming ~subst:subst2 a))
         v.IG.v_args
    and conclusion =
      U.eq
        (U.eval_renaming ~subst:subst1 v.IG.v_term)
        (U.eval_renaming ~subst:subst2 v.IG.v_term)
    in
    U.forall_l (vars1@vars2) (U.imply_l conds conclusion)
    |> CCOpt.return
  )

(* add the congruence axioms corresponding to instance graph [g], into [push_stmt] *)
let add_congruence_axioms push_stmt g =
  let module IG = InstanceGraph in
  (* axioms between "roots" (i.e. instances of [g.IG.id]
     that are the most general) *)
  let roots = InstanceGraph.roots g in
  begin
    Sequence.product roots roots
    |> Sequence.iter
      (fun (v1,v2) ->
         (* only emit an axiom once for every pair of distinct vertices *)
         if ID.compare v1.IG.v_id v2.IG.v_id < 0
         then (
           let ax = mk_congruence_axiom v1 v2 in
           push_stmt (Stmt.axiom1 ~info:Stmt.info_default ax)
         ))
  end;
  (* axioms between a specialized function and its parent (which is more
     general than itself) *)
  InstanceGraph.non_roots g
    (fun (v1,(sigma,v2)) ->
       (* [v2.term\sigma = v1.term], push the corresponding axiom *)
       let ax =
         U.eq
           (spec_term_of_vertex v1)
           (U.eval ~subst:sigma (spec_term_of_vertex v2))
         |> U.close_forall
       in
       push_stmt (Stmt.axiom1 ~info:Stmt.info_default ax));
  (* self-congruence axioms *)
  begin
    InstanceGraph.all_vertices g
    |> Sequence.filter_map mk_self_congruence
    |> Sequence.iter
      (fun ax -> push_stmt (Stmt.axiom1 ~info:Stmt.info_default ax))
  end;
  ()

(** {6 Main Encoding} *)

let specialize_problem pb =
  let state = create_state() in
  let trav =
    Trav.create
      ~env:(Env.create())
      ~dispatch
      ~state
      ()
  in
  (* transform *)
  Problem.iter_statements pb
    ~f:(fun st ->
      Trav.traverse_stmt
        ~after_env:(fun _ -> analyze_cg_st ~self:trav st)
        trav st);
  let res = Trav.get_statements trav in
  (* add congruence axioms for specialized functions that require it *)
  ID.Tbl.iter
    (fun id nfs ->
       if nfs.nfs_needs_congruence then (
         let ty = Env.find_ty_exn ~env:(Trav.env trav) id in
         let _, ty_args, _ = U.ty_unfold ty in
         let g = InstanceGraph.make id ty_args nfs.nfs_instances in
         Utils.debugf ~section 2 "%a" (fun k->k InstanceGraph.print g);
         add_congruence_axioms (CCVector.push res) g;
       ))
    state.new_funs;
  (* output new problem *)
  let pb' =
    Problem.make ~meta:(Problem.metadata pb) (CCVector.freeze res)
  in
  pb', state.decode

(** {2 Decoding}

    Decoding the model, that is, glue together the valuations of specialized
    functions to obtain the model of the function *)

module M = Model
module DT = M.DT
module DTU = M.DT_util

let is_spec_fun (state:decode_state) id = ID.Tbl.mem state id

let is_spec_const (state:decode_state) (t:T.t) = match T.repr t with
  | TI.Const id -> is_spec_fun state id
  | _ -> false

let find_spec (state:decode_state) id : decode_state_fun =
  try ID.Tbl.find state id
  with Not_found -> errorf "could not find the decoding data for %a" ID.print id

(* each element [i, t] of [args] is inserted in position [i] in [l]
   preconds:
   - [l] is large enough for every index of [arg]
   - [arg] is sorted by increasing index *)
let insert_pos l args : _ list =
  let rec aux i l args = match l, args with
    | [], [] -> []
    | [], (j,a)::args' when i=j -> a :: aux (i+1) [] args'
    | [], _::_ -> assert false
    | _, [] -> l (* no more args *)
    | _, (j,arg) :: args' when i=j ->
      arg :: aux (i+1) l args' (* insert here *)
    | (x :: l'), _ ->
      x :: aux (i+1) l' args (* later *)
  in
  aux 0 l args

let pp_dsf out dsf =
  fpf out "@[(spec %a on @[%a@])@]" ID.print dsf.dsf_spec_of Arg.print dsf.dsf_arg

(* convert a specialized function into a λ-term that evaluates to the
   non-specialized function when fully applied *)
let dsf_to_fun (dsf:decode_state_fun) : T.t =
  let _, ty_args, _ = U.ty_unfold dsf.dsf_ty_of in
  let arg = dsf.dsf_arg in
  (* arguments the unspecialized function will be applied to *)
  let unspec_args =
    List.mapi
      (fun i ty ->
         try
           let t = Arg.get i arg in
           `Spec t
         with Not_found ->
           `Var (Var.make ~ty ~name:(Printf.sprintf "arg_%d" i)))
      ty_args
  in
  (* variables we abstract on *)
  let vars =
    Arg.vars arg @
      CCList.filter_map (function `Spec _ -> None | `Var v -> Some v) unspec_args
  in
  let body =
    U.app
      (U.const dsf.dsf_spec_of)
      (List.map (function `Spec t -> t | `Var v -> U.var v) unspec_args)
  in
  let res = U.fun_l vars body in
  Utils.debugf ~section 5
    "@[<2>dsf_to_fun `@[%a@]`@ --> `@[%a@]`@]"
    (fun k->k pp_dsf dsf P.print res);
  assert (U.is_closed res);
  res

(* traverse the term and use reverse table to replace specialized
   functions by their definition *)
let rec decode_term_rec (state:decode_state) subst t =
  match T.repr t with
    | TI.Var v ->
      (* variable might not be bound, e.g. in skolem [_witness_of ...] *)
      Subst.find_or ~default:t ~subst v |> U.eval ~rec_:false ~subst
    | TI.Const f_id when is_spec_fun state f_id ->
      let dsf = find_spec state f_id in
      Utils.debugf ~section 5 "@[<2>decode `@[%a@]`@ from %a@]"
        (fun k->k P.print t pp_dsf dsf);
      dsf_to_fun dsf
    | TI.App (f, l) ->
      begin match T.repr f with
        | TI.Const f_id when is_spec_fun state f_id ->
          let dsf = find_spec state f_id in
          Utils.debugf ~section 5 "@[<2>decode `@[%a@]`@ from %a@]"
            (fun k->k P.print t pp_dsf dsf);
          (* decode arguments, and decode specialized function *)
          let l' = List.map (decode_term_rec state subst) l in
          let f' =
            dsf_to_fun dsf
            |> decode_term_rec state subst in
          Red.app_whnf ~subst f' l' |> Red.eta_reduce
        | _ -> decode_term_rec' state subst t
      end
    | _ -> decode_term_rec' state subst t

and decode_term_rec' state subst t =
  U.map subst t ~bind:U.rename_var ~f:(decode_term_rec state)

let decode_term state t : T.t =
  let t' = decode_term_rec state Subst.empty t in
  Utils.debugf ~section 5
    "@[<2>decode_term `@[%a@]`@ into `@[%a@]`@]" (fun k->k P.print t P.print t');
  t'

type aggregate_model = {
  am_kind: Model.symbol_kind;
  am_ty: ty; (* type of the function *)
  am_models: ((term, term) DT.t * decode_state_fun) list;
}

type aggregate_models = aggregate_model ID.Map.t

let am_empty k ty = {am_kind=k; am_ty=ty; am_models=[]}

(* gather models of specialized functions *)
let gather_spec_funs state m : aggregate_models =
  Model.fold ID.Map.empty m
    ~values:(fun map (t,dt,kind) -> match T.repr t with
      | TI.Const f_id when is_spec_fun state f_id ->
        (* add model of [f_id] into the list of partial models of the
           function it was specialized from *)
        let dsf = find_spec state f_id in
        let id = dsf.dsf_spec_of in
        let am =
          ID.Map.get_or id map ~or_:(am_empty kind dsf.dsf_ty_of)
        in
        let am = { am with am_models = (dt,dsf) :: am.am_models } in
        ID.Map.add id am map
      | _ -> map)

(* function that converts a specialized DT into a non-specialized DT,
   where terms are decoded *)
let dt_of_spec_dt state ~vars (dt,dsf) : (_,_) DT.t =
  Utils.debugf ~section 5
    "@[<2>generalize dt@ `@[<2>@[%a@]@]`@ on vars @[%a@]@ with arg %a@]"
    (fun k->k
        DTU.print dt (CCFormat.list Var.print_full) vars
        Arg.print dsf.dsf_arg);
  let n_closure_vars = List.length (Arg.vars dsf.dsf_arg) in
  assert (List.length (DT.vars dt)
    = List.length vars - Arg.length dsf.dsf_arg + n_closure_vars);
  let closure_vars, non_spec_vars =
    CCList.take_drop n_closure_vars (DT.vars dt)
  in
  (* add the specialized vars in front of [dt], in one single branch *)
  let spec_args =
    Arg.to_list dsf.dsf_arg
    |> List.map (fun (i,arg) -> i, List.nth vars i, arg)
  in
  let dt =
    List.fold_right
      (fun (_,v,arg) dt ->
         DT.cases v ~default:None ~tests:[arg, dt])
      spec_args dt
  in
  (* now pivot so that:
     - the closure vars come first
     - the remaining vars are in the pre-specialization order *)
  let vars' =
    insert_pos non_spec_vars (List.map (fun (i,v,_) ->i,v) spec_args)
  in
  assert (List.length vars' = List.length vars);
  let dt = DTU.reorder (closure_vars @ vars') dt in
  (* eliminate closure_vars *)
  let dt = DTU.remove_vars closure_vars dt in
  (* rename [vars'] into [vars], so we can merge later with other
     specialized trees *)
  let subst = Subst.of_list vars' vars in
  let dt = DTU.map_vars ~subst dt in
  (* decode terms *)
  let dt = DT.map dt ~ty:CCFun.id ~term:(decode_term state) in
  Utils.debugf ~section 5 "@[<2>... obtaining@ `@[<v>%a@]`@]"
    (fun k->k DTU.print dt);
  dt

(* TODO: if the function is also non-specialized, only take its model? *)

(* convert a set of specialized models, into a model of the
   non-specialized function *)
let dt_of_am state (am:aggregate_model) : (_,_) DT.t =
  let _, ty_args, _ = U.ty_unfold am.am_ty in
  let vars = List.mapi (fun i ty -> Var.makef ~ty "x_%d" i) ty_args in
  (* convert each specialized DT into a partial DT ranging over [vars] *)
  let dt_l =
    List.map
      (fun (dt, dsf) -> dt_of_spec_dt state ~vars (dt, dsf))
      am.am_models
  in
  let dt = DTU.merge_l dt_l in
  (* specialization is incomplete, so we might need a default case *)
  let default =
    U.app (U.undefined_atom ~ty:am.am_ty) (List.map U.var vars)
  in
  DT.add_default default dt

(* - merge models of specialized functions (possibly with main function)
   - remove specialized functions from the model
*)
let decode_model state m =
  let spec_funs = gather_spec_funs state m in
  (* remove specialized functions from model *)
  let m' =
    Model.filter_map m
      ~finite_types:(fun (t,l) -> match T.repr t with
        | TI.TyArrow (_,_) ->
          None (* remove arrow types, not finite types anymore *)
        | _ -> Some (t,l))
      ~values:(fun (t,dt,k) -> match T.repr t with
        | _ when is_spec_const state t -> None
        | TI.Const f_id when is_spec_fun state f_id ->
          None (* drop models of specialized funs *)
        | _ ->
          Utils.debugf ~section 5
            "@[<2>decode DT `@[%a@]`@]" (fun k->k DTU.print dt);
          let dt =
            DTU.rename_vars dt
            |> DT.map ~term:(decode_term_rec state Subst.empty) ~ty:CCFun.id
          in
          Some (t, dt, k)
      )
  in
  (* add functions that were specialized, after recombining their
     partial models *)
  ID.Map.fold
    (fun f_id am m ->
       let t = U.const f_id in
       let dt = dt_of_am state am in
       Utils.debugf ~section 3
         "@[<2>decoded DT for %a:@ %a@]"
         (fun k->k ID.print f_id DTU.print dt);
       Model.add_value m (t, dt, am.am_kind))
    spec_funs
    m'

(** {6 Integration in Transform} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module P = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after specialization@}: %a@]@." P.print)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono; Eqn, Eqn_single; Match, Present])
    ~on_encoded ?on_decoded
    ~encode:(fun pb ->
      let pb, decode = specialize_problem pb in
      pb, decode)
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after specialize@}:@ %a@]@."
         (Problem.Res.print P.print' P.print)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~on_decoded ~decode ~print ~check

