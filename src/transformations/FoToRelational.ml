
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

module TyTbl = CCHashtbl.Make(FO.Ty)

let name = "fo_to_rel"

type problem1 = (FO.T.t, FO.Ty.t) FO.Problem.t
type model1 = (FO.T.t, FO.Ty.t) Model.t

type problem2 = FO_rel.problem
type model2 = (FO_rel.expr, FO_rel.sub_universe) Model.t

let section = Utils.Section.(make ~parent:root) name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "in %s: %s" name msg)
      | _ -> None)

let error msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

(** {2 Encoding} *)

type domain = {
  dom_ty: FO.Ty.t;
  dom_id: ID.t; (* ID corresponding to the type *)
  dom_su: FO_rel.sub_universe;
}

type fun_encoding = {
  fun_ty_args: domain list;
  fun_low: FO_rel.tuple_set;
  fun_high: FO_rel.tuple_set;
  fun_is_pred: bool; (* predicate? *)
  fun_ty_ret: FO.Ty.t; (* return type, for decoding *)
}

type state = {
  mutable domains: domain TyTbl.t;
    (* atomic type -> domain *)
  funs: fun_encoding ID.Tbl.t;
    (* function -> relation *)
  dom_of_id: domain ID.Tbl.t;
    (* domain.dom_id -> domain *)
  pprop_dom: domain;
    (* specific domain for pseudo-prop *)
  ptrue: ID.t;
    (* pseudo-true : pseudo-prop *)
}

(* declaration of this function/relation *)
let decl_of_fun id f : FO_rel.decl =
  { FO_rel.
    decl_id=id;
    decl_arity=List.length f.fun_ty_args;
    decl_low=f.fun_low;
    decl_high=f.fun_high;
  }

(* declaration for the type contained in this sub-universe, if considered
   as a unary relation *)
let decl_of_su su : FO_rel.decl =
  { FO_rel.
    decl_id = su.FO_rel.su_name;
    decl_arity=1;
    decl_low=FO_rel.ts_list [];
    decl_high=FO_rel.ts_all su;
  }

let create_state () =
  let pprop_id = ID.make "pseudo-prop" in
  let ptrue = ID.make "pseudo-true" in
  let pprop_ty = FO.Ty.const pprop_id in
  let pprop_dom = {
    dom_ty=pprop_ty;
    dom_id=pprop_id;
    dom_su=FO_rel.su_make ~card:2 pprop_id;
  } in
  let state = {
    domains=TyTbl.create 16;
    funs=ID.Tbl.create 16;
    dom_of_id=ID.Tbl.create 16;
    pprop_dom;
    ptrue;
  } in
  (* declare ptrue *)
  let ptrue_fe = {
    fun_is_pred=false;
    fun_ty_args=[pprop_dom];
    fun_low=FO_rel.ts_list [];
    fun_high=FO_rel.ts_all pprop_dom.dom_su;
    fun_ty_ret=pprop_ty;
  } in
  ID.Tbl.add state.funs ptrue ptrue_fe;
  (* return *)
  state

(* create a new ID that will "stand" for this type *)
let id_of_ty ty : ID.t =
  let rec pp_ out t = match FO.Ty.view t with
    | FO.TyBuiltin b -> FO.TyBuiltin.print out b
    | FO.TyApp (a,[]) -> ID.print_name out a
    | FO.TyApp (a,l) ->
      Format.fprintf out "%a_%a"
        ID.print_name a
        (CCFormat.list ~start:"" ~stop:"" ~sep:"_" pp_) l
  in
  match FO.Ty.view ty with
    | FO.TyApp (id,[]) -> id
    | _ ->
      let n = CCFormat.sprintf "@[<h>%a@]" pp_ ty in
      ID.make n

(* ensure the type is declared *)
let declare_ty ?card state (ty:FO.Ty.t) =
  if TyTbl.mem state.domains ty
  then errorf "type `@[%a@]` declared twice" FO.print_ty ty;
  (* TODO: handle cardinality constraints *)
  let dom_id = id_of_ty ty in
  let su = FO_rel.su_make ?card dom_id in
  let dom = { dom_id; dom_ty=ty; dom_su=su; } in
  Utils.debugf ~section 3 "@[<2>declare type %a@ = {@[%a@]}@]"
    (fun k->k FO.print_ty ty FO_rel.print_sub_universe su);
  TyTbl.add state.domains ty dom;
  ID.Tbl.add state.dom_of_id dom_id dom;
  dom

(* [ty] is another pseudo-prop *)
let add_pseudo_prop state ty : unit =
  assert (not (TyTbl.mem state.domains ty));
  TyTbl.add state.domains ty state.pprop_dom;
  ()

(* type -> its domain *)
let domain_of_ty state (ty:FO.Ty.t) : domain =
  try TyTbl.find state.domains ty
  with Not_found -> declare_ty state ty

let su_of_ty state ty : FO_rel.sub_universe =
  (domain_of_ty state ty).dom_su

let declare_fun state id f =
  Utils.debugf ~section 3 "@[<2>declare function@ `@[%a@]`@]"
    (fun k->k FO_rel.print_decl (decl_of_fun id f));
  ID.Tbl.add state.funs id f

let fun_is_declared state id = ID.Tbl.mem state.funs id

let find_fun_ state id : fun_encoding option = ID.Tbl.get state.funs id

let app_fun_ id l =
  List.fold_left
    (fun f arg -> FO_rel.join arg f)
    (FO_rel.const id) l

(* term -> expr *)
let rec encode_term state t : FO_rel.expr =
  match FO.T.view t with
    | FO.Builtin (`Int _) -> assert false (* TODO *)
    | FO.Var v -> FO_rel.var (encode_var state v)
    | FO.App (f,l) ->
      begin match find_fun_ state f with
        | None ->
          errorf "function %a is undeclared" ID.print f;
        | Some {fun_is_pred=true; _} ->
          errorf "cannot encode predicate application@ `@[%a@]` as relation"
            FO.print_term t
        | Some _ ->
          let l = List.map (encode_term state) l in
          app_fun_ f l
      end
    | FO.DataTest (_,_)
    | FO.DataSelect (_,_,_) ->
      error "should have eliminated data{test/select} earlier"
    | FO.Undefined (_,t) -> encode_term state t
    | FO.Fun (_,_) ->
      errorf "cannot translate function `@[%a@]` to FO_rel" FO.print_term t
    | FO.Let (v,t,u) ->
      FO_rel.let_
        (encode_var state v) (encode_term state t) (encode_term state u)
    | FO.Ite (a,b,c) ->
      FO_rel.if_ (encode_form state a) (encode_term state b) (encode_term state c)
    | FO.True
    | FO.False
    | FO.Eq (_,_)
    | FO.And _
    | FO.Or _
    | FO.Not _
    | FO.Imply (_,_)
    | FO.Equiv (_,_)
    | FO.Forall (_,_)
    | FO.Exists (_,_) ->
      errorf "expected term,@ but `@[%a@]` is a formula" FO.print_term t
    | FO.Mu (_,_)
    | FO.Undefined_atom _
    | FO.Unparsable _ -> assert false

and encode_form state t : FO_rel.form =
  match FO.T.view t with
    | FO.Ite (a,b,c) ->
      let a = encode_form state a in
      let b = encode_form state b in
      let c = encode_form state c in
      FO_rel.or_
        (FO_rel.imply a b)
        (FO_rel.imply (FO_rel.not_ a) c)
    | FO.Eq (a,b) ->
      let a = encode_term state a in
      let b = encode_term state b in
      FO_rel.eq a b
    | FO.True -> FO_rel.true_
    | FO.False -> FO_rel.false_
    | FO.And l -> FO_rel.and_l (List.map (encode_form state) l)
    | FO.Or l -> FO_rel.or_l (List.map (encode_form state) l)
    | FO.Not f -> FO_rel.not_ (encode_form state f)
    | FO.Imply (a,b) ->
      let a = encode_form state a in
      let b = encode_form state b in
      FO_rel.imply a b
    | FO.Equiv (a,b) ->
      let a = encode_form state a in
      let b = encode_form state b in
      FO_rel.equiv a b
    | FO.Forall (v,f) ->
      FO_rel.for_all (encode_var state v) (encode_form state f)
    | FO.Exists (v,f) ->
      FO_rel.exists (encode_var state v) (encode_form state f)
    | FO.App (f, l) ->
      (* atomic formula. Two distinct encodings depending on whether
         it's a predicate or a function *)
      begin match find_fun_ state f with
        | None -> errorf "function %a is undeclared" ID.print f;
        | Some fun_ ->
          assert fun_.fun_is_pred; (* typing *)
          let l = List.map (encode_term state) l in
          begin match List.rev l with
            | [] ->
              (* nullary predicate: [pred] becomes [pred = ptrue_] *)
              FO_rel.eq (FO_rel.const f) (FO_rel.const state.ptrue)
            | last :: args ->
              (* [pred a b c] becomes [c in (b · (a · pred))];
                 here we remove the last argument *)
              let args = List.rev args in
              FO_rel.in_ last (app_fun_ f args)
          end
      end
    | FO.Builtin _
    | FO.Var _
    | FO.Mu (_,_)
    | FO.Undefined_atom _
    | FO.Unparsable _
    | FO.Fun (_,_)
    | FO.DataTest (_,_)
    | FO.DataSelect (_,_,_)
    | FO.Let (_,_,_)
    | FO.Undefined (_,_) ->
      (* atomic formula *)
      FO_rel.some (encode_term state t)

and encode_var state v =
  Var.update_ty v ~f:(su_of_ty state)

(* an axiom expressing the well-typedness of [f], if needed.
   For instance, for [cons : i -> list -> list], it will return
   [forall x:i y:list. some (y · x · cons · list)] *)
let ty_axiom state (f_id:ID.t) (ty_args : FO.Ty.t list) (ty_ret:FO.Ty.t) : FO_rel.form =
  assert (not (FO.Ty.is_prop ty_ret));
  let vars =
    List.mapi
      (fun i ty ->
         let d = domain_of_ty state ty in
         Var.makef ~ty:d.dom_su "x_%d" i)
      ty_args
  in
  let dom_ret = domain_of_ty state ty_ret in
  let t_fun = app_fun_ f_id (List.map FO_rel.var vars) in
  let t_ty = FO_rel.const dom_ret.dom_id in
  FO_rel.for_all_l vars (FO_rel.in_ t_fun t_ty)

let encode_statement state st : FO_rel.form list =
  let empty_domain = FO_rel.ts_list [] in
  let fun_domain (args:domain list) : FO_rel.tuple_set =
    args
    |> List.map (fun d -> FO_rel.ts_all d.dom_su)
    |> FO_rel.ts_product
  in
  match st with
    | FO.TyDecl (id, 0, attrs) when List.mem FO.Attr_pseudo_prop attrs ->
      add_pseudo_prop state (FO.Ty.const id);
      []
    | FO.TyDecl _ -> [] (* declared when used *)
    | FO.Decl (id, ([], _), attrs) when List.mem FO.Attr_pseudo_true attrs ->
      (* another pseudo-true *)
      let fe = {
        fun_is_pred=false;
        fun_ty_args=[state.pprop_dom];
        fun_low=FO_rel.ts_list [];
        fun_high=FO_rel.ts_all state.pprop_dom.dom_su;
        fun_ty_ret=state.pprop_dom.dom_ty;
      } in
      declare_fun state id fe;
      (* additional axiom: [id = true_] *)
      let ax = FO_rel.eq (FO_rel.const id) (FO_rel.const state.ptrue) in
      [ax]
    | FO.Decl (id, (ty_args, ty_ret), _) ->
      assert (not (fun_is_declared state id));
      (* encoding differs for relations and functions *)
      begin match FO.Ty.view ty_ret with
        | FO.TyBuiltin `Unitype -> assert false
        | FO.TyBuiltin `Prop when ty_args=[] ->
          (* nullary predicate -> unary predicate on pseudo-prop universe *)
          let fun_low = empty_domain in
          let fun_high = fun_domain [state.pprop_dom] in
          let f = {
            fun_is_pred=true;
            fun_ty_args=[];
            fun_low;
            fun_high;
            fun_ty_ret=ty_ret;
          } in
          declare_fun state id f;
          []
        | FO.TyBuiltin `Prop ->
          (* encode predicate as itself *)
          let fun_ty_args = List.map (domain_of_ty state) ty_args in
          let fun_low = empty_domain in
          let fun_high = fun_domain fun_ty_args in
          let f = {
            fun_is_pred=true;
            fun_ty_args;
            fun_low;
            fun_high;
            fun_ty_ret=ty_ret;
          } in
          declare_fun state id f;
          []
        | FO.TyApp _ ->
          (* function: encode as relation whose last argument is the return value *)
          let fun_ty_args =
            List.map (domain_of_ty state) ty_args @
              [domain_of_ty state ty_ret]
          in
          let fun_low = empty_domain in
          let fun_high = fun_domain fun_ty_args in
          let f = {
            fun_is_pred=false;
            fun_ty_args;
            fun_low;
            fun_high;
            fun_ty_ret=ty_ret;
          } in
          declare_fun state id f;
          (* return:
             - functionality axiom: [forall vars. one (id vars)]
             - typing axiom: [forall vars. (id vars) in ty_ret] *)
          let ax_functionality =
            let vars =
              List.mapi
                (fun i ty -> Var.makef ~ty:(su_of_ty state ty) "x_%d" i)
                ty_args
            in
            FO_rel.for_all_l vars
              (FO_rel.one
                 (app_fun_ id (List.map FO_rel.var vars)))
          and ax_typing =
            ty_axiom state id ty_args ty_ret
          in
          Utils.debugf ~section 3 "@[<2>functionality axiom for %a:@ `@[%a@]`@]"
            (fun k->k ID.print id FO_rel.print_form ax_functionality);
          Utils.debugf ~section 3 "@[<2>typing axiom for %a:@ `@[%a@]`@]"
            (fun k->k ID.print id FO_rel.print_form ax_typing);
          [ax_functionality; ax_typing]
      end
    | FO.Axiom f
    | FO.Goal f ->
      [encode_form state f]
    | FO.MutualTypes (_,_) ->
      errorf "unexpected (co)data@ `@[%a@]`" FO.print_statement st
    | FO.CardBound _ -> assert false (* TODO: merge with TyDecl...? *)

let encode_pb pb =
  let state = create_state () in
  let form =
    CCVector.flat_map_list (encode_statement state) (FO.Problem.statements pb)
    |> CCVector.to_list
  in
  (* axiom for ptrue: [one ptrue] *)
  let form = FO_rel.one (FO_rel.const state.ptrue) :: form in
  (* extract declarations: *)
  let decls =
    let d_funs =
      ID.Tbl.to_seq state.funs
      |> Sequence.map (CCFun.uncurry decl_of_fun)
    and d_types =
      TyTbl.values state.domains
      |> Sequence.map (fun d -> decl_of_su d.dom_su)
    in
    Sequence.append d_types d_funs
    |> CCVector.of_seq ?init:None
    |> CCVector.freeze
  in
  (* the universe *)
  let univ =
    { FO_rel.
      univ_prop=state.pprop_dom.dom_su;
      univ_l=
        TyTbl.values state.domains
        |> Sequence.map (fun d -> d.dom_su)
        |> Sequence.filter
          (fun su -> not (FO_rel.su_equal state.pprop_dom.dom_su su))
        |> Sequence.to_list
    }
  in
  let pb' =
    FO_rel.mk_problem
      ~meta:(FO.Problem.meta pb)
      ~univ
      ~decls
      ~goal:form
  in
  pb', state

(** {2 Decoding} *)

module DT = Model.DT

let rec tuples_of_ts ts: FO_rel.tuple Sequence.t = match ts with
  | FO_rel.TS_list l -> Sequence.of_list l
  | FO_rel.TS_product l ->
    let open Sequence.Infix in
    let rec aux l = match l with
      | [] -> assert false
      | [ts] -> tuples_of_ts ts
      | ts :: l' ->
        tuples_of_ts ts >>= fun tup ->
        aux l' >|= fun tup' -> tup @ tup'
    in
    aux l
  | FO_rel.TS_all _ -> assert false (* should not be in models *)

let atoms_of_ts ts: FO_rel.atom Sequence.t =
  tuples_of_ts ts |> Sequence.flat_map Sequence.of_list

let atoms_of_model m: FO_rel.atom Sequence.t =
  fun yield ->
    Model.iter m
    ~values:(fun (_,dt,_) -> match dt with
      | DT.Yield (FO_rel.Tuple_set set) -> atoms_of_ts set yield
      | _ -> assert false)

module AM = CCMap.Make(struct
    type t = FO_rel.atom
    let compare = FO_rel.atom_cmp
  end)

let rename_atoms m: ID.t AM.t =
  atoms_of_model m
  |> Sequence.sort_uniq ~cmp:FO_rel.atom_cmp
  |> Sequence.map
    (fun a ->
       let open FO_rel in
       let id =
         ID.make_f "%a_%d" ID.print_name a.a_sub_universe.su_name a.a_index
       in
       a, id)
  |> AM.of_seq

let id_of_atom_ map a : ID.t =
  try AM.find a map
  with Not_found ->
    errorf "could not find ID for atom `%a`" FO_rel.print_atom a

module M = Model

exception Found_ptrue of ID.t

(* find the atom corresponding to [pseudo-true] *)
let find_ptrue state map m : ID.t =
  try
    M.iter m
      ~values:(fun (t,set,_) -> match t with
        | FO_rel.Const id when ID.equal id state.ptrue ->
          begin match set with
            | DT.Yield (FO_rel.Tuple_set (FO_rel.TS_list [[a]])) ->
              let res = id_of_atom_ map a in
              raise (Found_ptrue res)
            | _ ->
              errorf "unexpected model for pseudo-true: `@[%a@]`"
                (DT.print (fun _ -> FO_rel.print_expr)) set
          end
        | _ -> ()
      );
    errorf "could not find pseudo-true in model"
  with Found_ptrue id -> id

(* [id = set] is in the model, and we know [id] corresponds to the function
   described in [fe] *)
let decode_fun_ ~ptrue ~ty_by_id map m id (fe:fun_encoding) (set:FO_rel.tuple_set) : model1 =
  let mk_vars doms =
    List.mapi (fun i d -> Var.makef "v_%d" i ~ty:d.dom_ty) doms
  in
  (* try to convert the atom into an ID, but return [None] if the atom
     does not belong to its type's domain *)
  let atom_to_id (a:FO_rel.atom) : ID.t option =
    let su = a.FO_rel.a_sub_universe in
    let id = id_of_atom_ map a in
    let _, ids = ID.Map.find su.FO_rel.su_name ty_by_id in
    if CCList.Set.mem ~eq:ID.equal id ids
    then Some id
    else None
  in
  let atom_to_id_exn a = match atom_to_id a with
    | None -> raise Exit
    | Some id -> id
  in
  (* convert a tuple to a list of ID, or None if the tuple was invalid
     (out of domain) *)
  let tup_to_ids (tup:FO_rel.tuple) : ID.t list option =
    try List.map atom_to_id_exn tup |> CCOpt.return
    with Exit -> None
  in
  let doms = fe.fun_ty_args in
  if fe.fun_is_pred
  then begin match doms with
    | [] ->
      (* constant predicate, actually sent as a unary predicate on [prop_].
         It is true iff it holds on [ptrue] *)
      let as_bool =
        tuples_of_ts set
        |> Sequence.exists
          (function
            | [a] -> ID.equal ptrue (id_of_atom_ map a)
            | _ -> false)
        |> (fun b -> if b then FO.T.true_ else FO.T.false_)
      in
      M.add_const m (FO.T.const id,as_bool,M.Symbol_prop)
    | _::_ ->
      (* predicate case *)
      let vars = mk_vars doms in
      (* the cases that lead to "true" *)
      let tests =
        tuples_of_ts set
        |> Sequence.filter_map
          (fun tup ->
             assert (List.length tup = List.length vars);
             match tup_to_ids tup with
               | None -> None
               | Some ids ->
                 let test =
                   List.map2
                     (fun v id -> DT.mk_flat_test v (FO.T.const id)) vars ids
                 in
                 Some (test, FO.T.true_))
        |> Sequence.to_list
      in
      let fdt =
        {M.DT.
          fdt_vars=vars;
          fdt_cases=tests;
          fdt_default=None;
        } in
      let dt = M.DT.of_flat ~equal:FO.T.equal ~hash:FO.T.hash fdt in
      let t' = FO.T.const id in
      Utils.debugf ~section 3
        "@[<2>decode predicate `%a`@ as `@[%a@]`@]"
        (fun k->k ID.print id (M.DT.print FO.print_term') dt);
      M.add_value m (t', dt, M.Symbol_prop)
  end else begin match List.rev doms with
    | [] -> assert false (* impossible, needs at least to return arg *)
    | [_dom_ret] ->
      (* constant: pick first element of the tuple(s) *)
      begin match tuples_of_ts set |> Sequence.to_list with
        | [[a]] ->
          let t = FO.T.const id in
          let u = FO.T.const (id_of_atom_ map a) in
          M.add_const m (t,u,M.Symbol_fun)
        | _ -> errorf "model for `%a` should have = 1 tuple" ID.print id
      end
    | _dom_ret :: args ->
      let dom_args = List.rev args in
      let vars = mk_vars dom_args in
      (* now build the test tree. We know by construction that every
         set of arguments has at most one return value *)
      let tests =
        tuples_of_ts set
        |> Sequence.filter_map
          (fun tup -> match List.rev tup with
             | [] -> assert false
             | ret :: args ->
               let args = List.rev args in
               assert (List.length args = List.length dom_args);
               let test = match tup_to_ids args with
                 | None -> None
                 | Some ids ->
                   let test =
                     List.map2
                       (fun v id -> DT.mk_flat_test v (FO.T.const id))
                       vars ids
                   in
                   Some test
               and ret = atom_to_id ret in
               match test, ret with
                 | None, _ | _, None -> None
                 | Some test, Some ret ->
                   Some (test, FO.T.const ret)
          )
        |> Sequence.to_list
      in
      let fdt =
        {M.DT.
          fdt_vars=vars;
          fdt_cases=tests;
          fdt_default=None;
        } in
      let dt = M.DT.of_flat ~equal:FO.T.equal ~hash:FO.T.hash fdt in
      let t' = FO.T.const id in
      Utils.debugf ~section 3
        "@[<2>decode function `%a`@ as `@[%a@]`@]"
        (fun k->k ID.print id (M.DT.print FO.print_term') dt);
      M.add_value m (t', dt, M.Symbol_fun)
  end

(* [id := set] is in the model, and we know [id] corresponds to the type
   in [dom]; return the corresponding list of IDs *)
let rec decode_ty_dom_ map id (dom:domain) (set:FO_rel.tuple_set) : ID.t list =
  match set with
    | FO_rel.TS_all _ -> assert false (* not in models *)
    | FO_rel.TS_list tups ->
      List.map
        (function
          | [a] -> id_of_atom_ map a
          | _ as tup ->
            errorf "expected unary tuple in model of `%a`, got `%a`"
              FO.print_ty dom.dom_ty FO_rel.print_tuple tup)
        tups
    | FO_rel.TS_product [set'] -> decode_ty_dom_ map id dom set'
    | FO_rel.TS_product _ ->
      (* should be a set of unary tuples *)
      errorf "in model of `%a`, expected a set of unary tuples"
        FO.print_ty dom.dom_ty

(* transform the constant relations into FO constants/functions/predicates *)
let decode_constants_ state ~ptrue (map:ID.t AM.t) m: (FO.T.t, FO.Ty.t) Model.t =
  (* map finite types to their domain *)
  let ty_by_id : (domain * ID.t list) ID.Map.t =
    M.values m
    |> Sequence.filter_map
      (fun (t,dt,_) -> match t, dt with
         | FO_rel.Const id, DT.Yield (FO_rel.Tuple_set set) ->
            begin match ID.Tbl.get state.dom_of_id id with
              | Some dom ->
                let ids = decode_ty_dom_ map id dom set in
                Some (dom.dom_id, (dom, ids))
              | None -> None
            end
         | _ -> None)
    |> ID.Map.of_seq
  in
  M.fold
    ~values:(fun m (t,dt,_) -> match t, dt with
      | FO_rel.Const id, _ when ID.equal id state.ptrue -> m (* remove from model *)
      | FO_rel.Const id, DT.Yield (FO_rel.Tuple_set set) ->
        begin match find_fun_ state id with
          | Some fe ->
            (* [id] is a function, decode it as such *)
            decode_fun_ ~ptrue ~ty_by_id map m id fe set
          | None ->
            if ID.equal id state.pprop_dom.dom_id
            then m (* ignore the pseudo-prop type *)
            else match ID.Map.get id ty_by_id with
              | Some (_, ids) ->
                M.add_finite_type m (FO.Ty.const id) ids
              | None ->
                errorf "`%a` is neither a function nor a type" ID.print id
        end
      | _ -> assert false)
    M.empty
    m

let decode state m =
  let map = rename_atoms m in
  let ptrue = find_ptrue state map m in
  Utils.debugf ~section 3  "@[<2>pseudo-true := %a in model@]" (fun k->k ID.print ptrue);
  decode_constants_ ~ptrue state map m

(** {2 Pipes} *)

let pipe_with ?on_decoded ~decode ~print =
  let input_spec =
    Transform.Features.(of_list [
        Match, Absent; Fun, Absent; Copy, Absent; Ind_preds, Absent;
        HOF, Absent; Prop_args, Absent])
  in
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after %s@}:@ %a@]@."
        name FO_rel.print_problem)
  in
  Transform.make ~name ~input_spec ?on_decoded ~on_encoded
    ~encode:encode_pb ~decode ()

let pipe ~print =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
         name (Problem.Res.print FO.print_term' FO.print_ty)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode state) in
  pipe_with ~on_decoded ~decode ~print

