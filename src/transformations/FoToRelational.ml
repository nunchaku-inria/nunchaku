
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
  fun_encoded_args: FO_rel.sub_universe list; (* for decoding *)
  fun_low: FO_rel.tuple_set;
  fun_high: FO_rel.tuple_set;
  fun_is_pred: bool; (* predicate? *)
  fun_ty_ret: FO.Ty.t; (* return type, for decoding *)
}

type state = {
  domains: domain TyTbl.t;
  (* atomic type -> domain *)
  funs: fun_encoding ID.Tbl.t;
  (* function -> relation *)
  dom_of_id: domain ID.Tbl.t;
  (* domain.dom_id -> domain *)
  pprop_dom: domain;
  (* specific domain for pseudo-prop *)
  ptrue: ID.t;
  (* pseudo-true : pseudo-prop *)
  ty_cards: int ID.Tbl.t;
  (* type -> exact cardinal, when available *)
}

(* declaration of this function/relation *)
let decl_of_fun id f : FO_rel.decl =
  { FO_rel.
    decl_id=id;
    decl_arity=List.length f.fun_ty_args;
    decl_dom=f.fun_encoded_args;
    decl_low=f.fun_low;
    decl_high=f.fun_high;
  }

(* declaration for the type contained in this sub-universe, if considered
   as a unary relation *)
let decl_of_su su : FO_rel.decl =
  { FO_rel.
    decl_id = su.FO_rel.su_name;
    decl_arity=1;
    decl_dom=[su];
    decl_low=FO_rel.ts_list [];
    decl_high=FO_rel.ts_all su;
  }

let find_pprop pb : ID.t =
  let ret =
    CCVector.find_map
      (fun st -> match st with
         | FO.TyDecl (id, 0, attrs) when List.mem FO.Attr_pseudo_prop attrs ->
           Some id
         | _ -> None)
      (FO.Problem.statements pb)
  in
  match ret with
    | None -> errorf "cannot find `pseudo-prop` in problem"
    | Some r -> r

let find_ptrue pb : ID.t =
  let ret =
    CCVector.find_map
      (fun st -> match st with
         | FO.Decl (id, ([], _), attrs) when List.mem FO.Attr_pseudo_true attrs ->
           Some id
         | _ -> None)
      (FO.Problem.statements pb)
  in
  match ret with
    | None -> errorf "cannot find `pseudo-prop` in problem"
    | Some r -> r

let create_state ~pprop ~ptrue () =
  let pprop_ty = FO.Ty.const pprop in
  let pprop_dom = {
    dom_ty=pprop_ty;
    dom_id=pprop;
    dom_su=FO_rel.su_make ~min_card:2 ~max_card:2 pprop;
  } in
  let state = {
    domains=TyTbl.create 16;
    funs=ID.Tbl.create 16;
    dom_of_id=ID.Tbl.create 16;
    pprop_dom;
    ptrue;
    ty_cards=ID.Tbl.create 8;
  } in
  (* declare ptrue *)
  let ptrue_fe = {
    fun_is_pred=false;
    fun_encoded_args=[pprop_dom.dom_su];
    fun_ty_args=[pprop_dom];
    fun_low=FO_rel.ts_list [];
    fun_high=FO_rel.ts_all pprop_dom.dom_su;
    fun_ty_ret=pprop_ty;
  } in
  ID.Tbl.add state.funs ptrue ptrue_fe;
  TyTbl.add state.domains pprop_ty pprop_dom;
  (* return *)
  state

(* create a new ID that will "stand" for this type *)
let id_of_ty ty : ID.t =
  let rec pp_ out t = match FO.Ty.view t with
    | FO.TyBuiltin b -> FO.TyBuiltin.pp out b
    | FO.TyApp (a,[]) -> ID.pp_name out a
    | FO.TyApp (a,l) ->
      Format.fprintf out "%a_%a"
        ID.pp_name a
        (Utils.pp_list ~sep:"_" pp_) l
  in
  match FO.Ty.view ty with
    | FO.TyApp (id,[]) -> id
    | _ ->
      let n = CCFormat.sprintf "@[<h>%a@]" pp_ ty in
      ID.make n

(* ensure the type is declared *)
let declare_ty state (ty:FO.Ty.t) =
  if TyTbl.mem state.domains ty then (
    errorf "type `@[%a@]` declared twice" FO.pp_ty ty;
  );
  (* create domain *)
  let dom_id = id_of_ty ty in
  let su = FO_rel.su_make dom_id in
  let dom = { dom_id; dom_ty=ty; dom_su=su; } in
  Utils.debugf ~section 3 "@[<2>declare type %a@ = {@[%a@]}@]"
    (fun k->k FO.pp_ty ty FO_rel.pp_sub_universe su);
  TyTbl.add state.domains ty dom;
  ID.Tbl.add state.dom_of_id dom_id dom;
  dom

(* type -> its domain *)
let domain_of_ty state (ty:FO.Ty.t) : domain =
  try TyTbl.find state.domains ty
  with Not_found -> declare_ty state ty

let update_sub_universe state ~f ty =
  let dom = domain_of_ty state ty in
  let dom = { dom with dom_su = f dom.dom_su; } in
  TyTbl.replace state.domains ty dom

let update_min_card state (ty:FO.Ty.t) (n:int): unit =
  Utils.debugf ~section 3 "@[<2>set minimum cardinality of type %a@ to %d@]"
    (fun k->k FO.pp_ty ty n);
  update_sub_universe state ty ~f:(fun su ->
    {su with FO_rel.su_min_card = max n su.FO_rel.su_min_card})

let update_max_card state (ty:FO.Ty.t) (n:int): unit =
  Utils.debugf ~section 3 "@[<2>set maximum cardinality of type %a@ to %d@]"
    (fun k->k FO.pp_ty ty n);
  update_sub_universe state ty ~f:(fun su ->
    {su with FO_rel.su_max_card = Some (match su.FO_rel.su_max_card with
       | None -> n
       | Some m -> min m n)})

let su_of_ty state ty : FO_rel.sub_universe =
  (domain_of_ty state ty).dom_su

let declare_fun state id f =
  Utils.debugf ~section 3 "@[<2>declare function@ `@[%a@]`@]"
    (fun k->k FO_rel.pp_decl (decl_of_fun id f));
  ID.Tbl.add state.funs id f

let fun_is_declared state id = ID.Tbl.mem state.funs id

let find_fun_ state id : fun_encoding option = ID.Tbl.get state.funs id

let app_fun_ id l =
  List.fold_left
    (fun f arg -> FO_rel.join arg f)
    (FO_rel.const id) l

type ('e, 'f) encode_res_p =
  | R_expr of 'e
  | R_form of 'f

let ret_form f = R_form f
let ret_expr e = R_expr e

type encode_res = (FO_rel.expr, FO_rel.form) encode_res_p

let as_pair_ (r1: encode_res) (r2: encode_res) : (_,_) encode_res_p = match r1, r2 with
  | R_expr e1, R_expr e2 -> R_expr (e1, e2)
  | R_expr e, R_form f -> R_form (FO_rel.some e, f)
  | R_form f, R_expr e -> R_form (f, FO_rel.some e)
  | R_form f1, R_form f2 -> R_form (f1, f2)

let encode_ty state ty: FO_rel.expr =
  let dom = domain_of_ty state ty in
  FO_rel.const dom.dom_id

(* encode this term into a relation expression or formula *)
let rec encode state (t:FO.T.t) : encode_res = match FO.T.view t with
  | FO.Ite (a,b,c) ->
    let a = encode_form state a in
    let b = encode state b in
    let c = encode state c in
    begin match as_pair_ b c with
      | R_expr (b,c) -> R_expr (FO_rel.if_ a b c)
      | R_form (b,c) -> R_form (FO_rel.f_if a b c)
    end
  | FO.Eq (a,b) ->
    let a = encode state a in
    let b = encode state b in
    begin match as_pair_ a b with
      | R_expr (a,b) -> FO_rel.eq a b |> ret_form
      | R_form (a,b) -> FO_rel.equiv a b |> ret_form
    end
  | FO.Let (v,a,b) ->
    let v = encode_var state v in
    let a = encode_term state a in
    let b = encode state b in
    begin match b with
      | R_expr b -> FO_rel.let_ v a b |> ret_expr
      | R_form b -> FO_rel.f_let v a b |> ret_form
    end
  | FO.True -> ret_form FO_rel.true_
  | FO.False -> ret_form FO_rel.false_
  | FO.And l -> FO_rel.and_l (List.map (encode_form state) l) |> ret_form
  | FO.Or l -> FO_rel.or_l (List.map (encode_form state) l) |> ret_form
  | FO.Not f -> FO_rel.not_ (encode_form state f) |> ret_form
  | FO.Imply (a,b) ->
    let a = encode_form state a in
    let b = encode_form state b in
    FO_rel.imply a b |> ret_form
  | FO.Equiv (a,b) ->
    let a = encode_form state a in
    let b = encode_form state b in
    FO_rel.equiv a b |> ret_form
  | FO.Forall (v,f) ->
    FO_rel.for_all (encode_var state v) (encode_form state f) |> ret_form
  | FO.Exists (v,f) ->
    FO_rel.exists (encode_var state v) (encode_form state f) |> ret_form
  | FO.App (f, l) ->
    (* atomic formula. Two distinct encodings depending on whether
       it's a predicate or a function *)
    begin match find_fun_ state f with
      | None -> errorf "function %a is undeclared" ID.pp f;
      | Some {fun_is_pred=true; _} ->
        let l = List.map (encode_term state) l in
        begin match List.rev l with
          | [] ->
            (* nullary predicate: [pred] becomes [pred = ptrue_] *)
            FO_rel.eq (FO_rel.const f) (FO_rel.const state.ptrue) |> ret_form
          | last :: args ->
            (* [pred a b c] becomes [c in (b · (a · pred))];
               here we remove the last argument *)
            let args = List.rev args in
            FO_rel.in_ last (app_fun_ f args) |> ret_form
        end
      | Some _ ->
        let l = List.map (encode_term state) l in
        app_fun_ f l |> ret_expr
    end
  | FO.Builtin (`Int _) -> assert false (* TODO *)
  | FO.Var v -> FO_rel.var (encode_var state v) |> ret_expr
  | FO.Card_at_least (ty, n) ->
    (* card(ty) >= n *)
    let ty = encode_ty state ty in
    FO_rel.int_leq (FO_rel.int_const n) (FO_rel.int_card ty) |> ret_form
  | FO.DataTest (_,_)
  | FO.DataSelect (_,_,_) ->
    error "should have eliminated data{test/select} earlier"
  | FO.Undefined t -> encode state t
  | FO.Fun (_,_) ->
    errorf "cannot translate function `@[%a@]` to FO_rel" FO.pp_term t
  | FO.Mu (_,_)
  | FO.Undefined_atom _
  | FO.Unparsable _ -> assert false

and encode_var state v =
  Var.update_ty v ~f:(su_of_ty state)

and encode_form state t: FO_rel.form =
  match encode state t with
    | R_form f -> f
    | R_expr e -> FO_rel.some e

and encode_term state t: FO_rel.expr =
  match encode state t with
    | R_expr e -> e
    | R_form _ ->
      errorf "@[<2>expected term,@ got formula @[%a@]@]" FO.pp_term t

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
  let t_fun = app_fun_ f_id (List.map FO_rel.var vars) in
  let t_ty = encode_ty state ty_ret in
  FO_rel.for_all_l vars (FO_rel.in_ t_fun t_ty)

let encode_statement state st : FO_rel.form list =
  let empty_domain = FO_rel.ts_list [] in
  let fun_domain (args:domain list) : FO_rel.tuple_set =
    args
    |> List.map (fun d -> FO_rel.ts_all d.dom_su)
    |> FO_rel.ts_product
  in
  match st with
    | FO.TyDecl (_, 0, attrs) when List.mem FO.Attr_pseudo_prop attrs ->
      []
    | FO.Decl (_, ([], _), attrs) when List.mem FO.Attr_pseudo_true attrs ->
      []
    | FO.TyDecl (id, 0, attrs) ->
      let ty = FO.Ty.const id in
      List.iter
        (function
           | FO.Attr_card_hint (`Max, n) ->
             update_max_card state ty n
           | FO.Attr_card_hint (`Min, n) ->
             update_min_card state ty n
           | _ -> ())
        attrs;
      let can_be_empty =
        List.exists (function FO.Attr_can_be_empty -> true | _ -> false) attrs
      in
      (* ensure there is at least one element… unless the type is allowed to be empty *)
      if can_be_empty then [] (* declared when used *)
      else (
        (* add statement [card(ty) ≥ 1] *)
        let ty = encode_ty state ty in
        [ FO_rel.some ty ]
      )
    | FO.TyDecl (_,_,_) -> [] (* ignore, will be mangled *)
    | FO.Decl (id, (ty_args, ty_ret), _) ->
      assert (not (fun_is_declared state id));
      (* encoding differs for relations and functions *)
      begin match FO.Ty.view ty_ret with
        | FO.TyBuiltin `Unitype -> assert false
        | FO.TyBuiltin `Prop when ty_args=[] ->
          (* nullary predicate: encoded unary predicate on pseudo-prop
             universe.
             NOTE: ty_args=[], but encoded_args=[pprop] *)
          let fun_low = empty_domain in
          let fun_high = fun_domain [state.pprop_dom] in
          let f = {
            fun_is_pred=true;
            fun_ty_args=[];
            fun_encoded_args=[state.pprop_dom.dom_su];
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
            fun_encoded_args=List.map (fun d->d.dom_su) fun_ty_args;
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
            fun_encoded_args=List.map (fun d->d.dom_su) fun_ty_args;
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
            (fun k->k ID.pp id FO_rel.pp_form ax_functionality);
          Utils.debugf ~section 3 "@[<2>typing axiom for %a:@ `@[%a@]`@]"
            (fun k->k ID.pp id FO_rel.pp_form ax_typing);
          [ax_functionality; ax_typing]
      end
    | FO.Axiom f
    | FO.Goal f ->
      [encode_form state f]
    | FO.MutualTypes (_,_) ->
      errorf "unexpected (co)data@ `@[%a@]`" FO.pp_statement st
    | FO.CardBound (id, k, n) ->
      (* the relation representing this type *)
      let ty = FO.Ty.const id in
      let dom = domain_of_ty state ty in
      let card_expr = FO_rel.int_card (FO_rel.const dom.dom_id) in
      let n' = FO_rel.int_const n in
      begin match k with
        | `Max ->
          update_max_card state ty n;
          [FO_rel.int_leq card_expr n']
        | `Min ->
          update_min_card state ty n;
          [FO_rel.int_leq n' card_expr]
      end

let encode_pb pb =
  let pprop = find_pprop pb in
  let ptrue = find_ptrue pb in
  let state = create_state ~ptrue ~pprop () in
  let form =
    CCVector.flat_map_list (encode_statement state) (FO.Problem.statements pb)
    |> CCVector.to_list
  in
  (* axiom for ptrue: [one ptrue], [ptrue in pprop] *)
  let form =
    FO_rel.one (FO_rel.const state.ptrue)
    :: FO_rel.in_ (FO_rel.const state.ptrue) (FO_rel.const state.pprop_dom.dom_id)
    :: form
  in
  (* extract declarations: *)
  let decls =
    let d_funs =
      ID.Tbl.to_seq state.funs
      |> Sequence.map (CCFun.uncurry decl_of_fun)
    and d_types =
      TyTbl.values state.domains
      |> Sequence.map (fun d -> d.dom_su)
      |> Sequence.sort_uniq ~cmp:FO_rel.su_compare
      |> Sequence.map decl_of_su
    in
    Sequence.append d_types d_funs
    |> Sequence.map (fun d -> d.FO_rel.decl_id, d)
    |> ID.Map.of_seq
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
         ID.make_f "%a_%d" ID.pp_name a.a_sub_universe.su_name a.a_index
       in
       a, id)
  |> AM.of_seq

let id_of_atom_ map a : ID.t =
  try AM.find a map
  with Not_found ->
    errorf "could not find ID for atom `%a`" FO_rel.pp_atom a

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
                (DT.pp (fun _ -> FO_rel.pp_expr) FO_rel.pp_sub_universe) set
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
    let ids =
      try ID.Map.find su.FO_rel.su_name ty_by_id
      with Not_found ->
        errorf "could not find domain of type %a@ in @[%a@]"
          ID.pp su.FO_rel.su_name
          (Utils.pp_seq CCFormat.Dump.(pair ID.pp (list ID.pp)))
          (ID.Map.to_seq ty_by_id)
    in
    if CCList.mem ~eq:ID.equal id ids
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
          fdt_default=Some FO.T.false_;
        } in
      let dt = M.DT.of_flat ~equal:FO.T.equal ~hash:FO.T.hash fdt in
      let t' = FO.T.const id in
      Utils.debugf ~section 3
        "@[<2>decode predicate `%a`@ as `@[%a@]`@]"
        (fun k->k ID.pp id (M.DT.pp FO.pp_term' FO.pp_ty) dt);
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
        | _ -> errorf "model for `%a` should have = 1 tuple" ID.pp id
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
      (* default case: undefined *)
      let default =
        let id = ID.make "_" in
        let ty = List.map (fun d-> d.dom_ty) fe.fun_ty_args, fe.fun_ty_ret in
        FO.T.undefined_atom id ty (List.map FO.T.var vars)
      in
      let fdt =
        {M.DT.
          fdt_vars=vars;
          fdt_cases=tests;
          fdt_default=Some default;
        } in
      let dt = M.DT.of_flat ~equal:FO.T.equal ~hash:FO.T.hash fdt in
      let t' = FO.T.const id in
      Utils.debugf ~section 3
        "@[<2>decode function `%a`@ as `@[%a@]`@]"
        (fun k->k ID.pp id (M.DT.pp FO.pp_term' FO.pp_ty) dt);
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
              FO.pp_ty dom.dom_ty FO_rel.pp_tuple tup)
        tups
    | FO_rel.TS_product [set'] -> decode_ty_dom_ map id dom set'
    | FO_rel.TS_product _ ->
      (* should be a set of unary tuples *)
      errorf "in model of `%a`, expected a set of unary tuples"
        FO.pp_ty dom.dom_ty

(* transform the constant relations into FO constants/functions/predicates *)
let decode_constants_ state ~ptrue (map:ID.t AM.t) m: (FO.T.t, FO.Ty.t) Model.t =
  (* map finite types to their domain *)
  let ty_by_id : ID.t list ID.Map.t =
    M.values m
    |> Sequence.filter_map
      (fun (t,dt,_) -> match t, dt with
         | FO_rel.Const id, DT.Yield (FO_rel.Tuple_set set) ->
           begin match ID.Tbl.get state.dom_of_id id with
             | Some dom ->
               let ids = decode_ty_dom_ map id dom set in
               Some (dom.dom_id, ids)
             | None when ID.equal id state.pprop_dom.dom_id ->
               let ids = decode_ty_dom_ map id state.pprop_dom set in
               Some (id, ids)
             | None -> None
           end
         | _ -> None)
    |> ID.Map.of_seq
  in
  M.fold
    ~values:(fun m (t,dt,_) -> match t, dt with
      | FO_rel.Const id, DT.Yield (FO_rel.Tuple_set set) ->
        begin match find_fun_ state id with
          | Some fe ->
            (* [id] is a function, decode it as such *)
            decode_fun_ ~ptrue ~ty_by_id map m id fe set
          | None ->
            if ID.equal id state.pprop_dom.dom_id
            then m (* ignore the pseudo-prop type *)
            else match ID.Map.get id ty_by_id with
              | Some ids ->
                M.add_finite_type m (FO.Ty.const id) ids
              | None ->
                errorf "`%a` is neither a function nor a type" ID.pp id
        end
      | _ -> assert false)
    M.empty
    m

let decode state m =
  let map = rename_atoms m in
  let ptrue = find_ptrue state map m in
  Utils.debugf ~section 3  "@[<2>pseudo-true := %a in model@]" (fun k->k ID.pp ptrue);
  decode_constants_ ~ptrue state map m

(** {2 Pipes} *)

let pipe_with ?on_decoded ~decode ~print =
  let input_spec =
    Transform.Features.(of_list [
        Match, Absent; Fun, Absent; Copy, Absent; Ind_preds, Absent;
        HOF, Absent; Prop_args, Absent; Pseudo_prop, Present])
  in
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after %s@}:@ %a@]@."
        name FO_rel.pp_problem)
  in
  Transform.make ~name ~input_spec ?on_decoded ~on_encoded
    ~encode:encode_pb ~decode ()

let pipe ~print =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
         name (Problem.Res.pp FO.pp_term' FO.pp_ty)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode state) in
  pipe_with ~on_decoded ~decode ~print

