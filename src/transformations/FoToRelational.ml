
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
  domain_size: int;
    (* size of domains *)
  mutable domains: domain TyTbl.t;
    (* atomic type -> domain *)
  funs: fun_encoding ID.Tbl.t;
    (* function -> relation *)
}

(* declaration of this function/relation *)
let decl_of_fun id f =
  { FO_rel.
    decl_id=id;
    decl_arity=List.length f.fun_ty_args;
    decl_low=f.fun_low;
    decl_high=f.fun_high;
  }

let create_state ~size () =
  let state = {
    domain_size=size;
    domains=TyTbl.create 16;
    funs=ID.Tbl.create 16;
  } in
  state

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
let declare_ty state (ty:FO.Ty.t) =
  if TyTbl.mem state.domains ty
  then errorf "type `@[%a@]` declared twice" FO.print_ty ty;
  (* TODO: handle cardinality constraints *)
  let dom_id = id_of_ty ty in
  let su = FO_rel.su_make dom_id ~card:state.domain_size in
  let dom = { dom_id; dom_ty=ty; dom_su=su; } in
  Utils.debugf ~section 3 "@[<2>declare type %a@ = {@[%a@]}@]"
    (fun k->k FO.print_ty ty FO_rel.print_sub_universe su);
  TyTbl.add state.domains ty dom;
  dom

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

let ty_is_declared state ty: bool = TyTbl.mem state.domains ty

let fun_is_declared state id = ID.Tbl.mem state.funs id

let find_fun_ state id : fun_encoding option = ID.Tbl.get state.funs id

let app_fun_ id l =
  List.fold_left
    (fun f arg -> FO_rel.join arg f)
    (FO_rel.const id) l

(* term -> expr *)
let rec encode_term state t : FO_rel.expr =
  match FO.T.view t with
    | FO.Builtin _ -> assert false (* TODO *)
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
    | FO.Undefined (_,_) -> assert false (* TODO? *)
    | FO.Fun (_,_) ->
      errorf "cannot translate function `@[%a@]` to FO_rel" FO.print_term t
    | FO.Let (_,_,_) -> assert false (* TODO: expand *)
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
    | FO.Let (_,_,_) -> assert false (* TODO: expand *)
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
              (* [pred] becomes [some pred] *)
              FO_rel.some (FO_rel.const f)
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
    | FO.Undefined (_,_) ->
      (* atomic formula *)
      FO_rel.some (encode_term state t)

and encode_var state v =
  Var.update_ty v ~f:(su_of_ty state)

let encode_statement state st : FO_rel.form option =
  let empty_domain = FO_rel.ts_list [] in
  let fun_domain (args:domain list) : FO_rel.tuple_set =
    args
    |> List.map (fun d -> FO_rel.ts_all d.dom_su)
    |> FO_rel.ts_product
  in
  match st with
    | FO.TyDecl _ -> None (* declared when used *)
    | FO.Decl (id, (ty_args, ty_ret)) ->
      assert (not (fun_is_declared state id));
      (* encoding differs for relations and functions *)
      begin match FO.Ty.view ty_ret with
        | FO.TyBuiltin `Unitype -> assert false
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
          None
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
          (* return functionality axiom:
             [forall vars. one (id vars)] *)
          let ax =
            let vars =
              List.mapi
                (fun i ty -> Var.makef ~ty:(su_of_ty state ty) "x_%d" i)
                ty_args
            in
            FO_rel.for_all_l vars
              (FO_rel.one
                 (app_fun_ id (List.map FO_rel.var vars)))
          in
          Utils.debugf ~section 3 "@[<2>functionality axiom for %a:@ `@[%a@]`@]"
            (fun k->k ID.print id FO_rel.print_form ax);
          Some ax
      end
    | FO.Axiom f
    | FO.Goal f ->
      Some (encode_form state f)
    | FO.MutualTypes (_,_) ->
      errorf "unexpected (co)data@ `@[%a@]`" FO.print_statement st
    | FO.CardBound _ -> assert false (* TODO: merge with TyDecl...? *)

let encode_pb pb =
  let state = create_state ~size:10 () in
  let form =
    CCVector.filter_map (encode_statement state) (FO.Problem.statements pb)
    |> CCVector.to_list
  in
  (* extract declarations *)
  let decls =
    ID.Tbl.to_seq state.funs
    |> Sequence.map (CCFun.uncurry decl_of_fun)
    |> CCVector.of_seq ?init:None
    |> CCVector.freeze
  in
  (* the universe *)
  let univ =
    TyTbl.values state.domains
    |> Sequence.map (fun d -> d.dom_su)
    |> Sequence.to_list
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

let atoms_of_su su: FO_rel.atom Sequence.t =
  let open Sequence.Infix in
  0 -- (su.FO_rel.su_card-1)
  |> Sequence.map (fun i -> FO_rel.atom su i)

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
  | FO_rel.TS_all su ->
    atoms_of_su su |> Sequence.map CCList.return

let atoms_of_ts ts: FO_rel.atom Sequence.t =
  tuples_of_ts ts |> Sequence.flat_map Sequence.of_list

let atoms_of_model m: FO_rel.atom Sequence.t =
  fun yield ->
    Model.iter m
    ~constants:(fun (_,u,_) -> match u with
      | FO_rel.Tuple_set set -> atoms_of_ts set yield
      | _ -> assert false)

module AM = CCMap.Make(struct
    type t = FO_rel.atom
    let compare = FO_rel.atom_cmp
  end)

let rename_atoms m: ID.t AM.t =
  atoms_of_model m
  |> Sequence.sort_uniq ~cmp:FO_rel.atom_cmp
  |> Sequence.mapi (fun i a -> a, ID.make_f "atom_%d" i)
  |> AM.of_seq

let id_of_atom_ map a : ID.t =
  try AM.find a map
  with Not_found ->
    errorf "could not find ID for atom `%a`" FO_rel.print_atom a

(* transform the constant relations into FO constants/functions/predicates *)
let decode_constants_ state (map:ID.t AM.t) m: (FO.T.t, FO.Ty.t) Model.t =
  let module M = Model in
  let mk_vars doms =
    List.mapi (fun i d -> Var.makef "v_%d" i ~ty:d.dom_ty) doms
  in
  M.fold
    ~constants:(fun m (t,u,_) -> match t, u with
      | FO_rel.Const id, FO_rel.Tuple_set set ->
        let fe = match find_fun_ state id with
          | Some fe -> fe
          | None -> assert false
        in
        let doms = fe.fun_ty_args in
        if fe.fun_is_pred
        then (
          (* FIXME: constant predicate...? *)
          (* predicate case *)
          assert (doms <> []);
          let vars = mk_vars doms in
          (* the cases that lead to "true" *)
          let cases =
            tuples_of_ts set
            |> Sequence.map
              (fun tup ->
                 assert (List.length tup = List.length vars);
                 let test =
                   List.map2
                     (fun v a -> v, FO.T.const (id_of_atom_ map a))
                     vars tup
                 in
                 test, FO.T.true_)
            |> Sequence.to_list
          and else_ =
            FO.T.false_
          in
          let dt = M.DT.test cases ~else_ in
          let t' = FO.T.const id in
          Utils.debugf ~section 3
            "@[<2>decode predicate `%a`@ as `@[%a@]`@]"
            (fun k->k ID.print id (M.DT.print FO.print_term') dt);
          M.add_fun m (t',vars,dt,M.Symbol_prop)
        ) else begin match List.rev doms with
          | [] -> assert false (* impossible, need at least return arg *)
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
            let cases =
              tuples_of_ts set
              |> Sequence.map
                (fun tup -> match List.rev tup with
                   | [] -> assert false
                   | ret :: args ->
                     let args = List.rev args in
                     assert (List.length args = List.length dom_args);
                     let test =
                       List.map2
                         (fun v a -> v, FO.T.const (id_of_atom_ map a))
                         vars args
                     in
                     let ret = FO.T.const (id_of_atom_ map ret) in
                     test, ret)
              |> Sequence.to_list
            and else_ =
              FO.T.undefined_atom id fe.fun_ty_ret (List.map FO.T.var vars)
            in
            let dt = M.DT.test cases ~else_ in
            let t' = FO.T.const id in
            Utils.debugf ~section 3
              "@[<2>decode function `%a`@ as `@[%a@]`@]"
              (fun k->k ID.print id (M.DT.print FO.print_term') dt);
            M.add_fun m (t',vars,dt,M.Symbol_fun)
        end
      | _ -> assert false)
    M.empty
    m

(* declare the types, retaining only the atoms that actually appear in
   the model *)
let add_types state map m : _ Model.t =
  TyTbl.to_seq state.domains
  |> Sequence.map
    (fun (ty, dom) ->
       let dom' =
         atoms_of_su dom.dom_su
         |> Sequence.filter_map (fun a -> AM.get a map)
         |> Sequence.to_rev_list
       in
       ty, dom')
  |> Sequence.fold
    (fun m (ty,dom) -> Model.add_finite_type m ty dom)
    m

let decode state m =
  let map = rename_atoms m in
  let m' = decode_constants_ state map m in
  add_types state map m'

(** {2 Pipes} *)

let pipe_with ~decode ~print =
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
  Transform.make ~name ~input_spec ~on_encoded ~encode:encode_pb ~decode ()

let pipe ~print =
  let decode state = Problem.Res.map_m ~f:(decode state) in
  pipe_with ~decode ~print

