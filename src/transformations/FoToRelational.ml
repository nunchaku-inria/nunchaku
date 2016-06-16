
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

type fun_ = {
  fun_ty_args: FO_rel.sub_universe list;
  fun_low: FO_rel.tuple_set;
  fun_high: FO_rel.tuple_set;
  fun_is_pred: bool; (* predicate? *)
}

(* declaration of this function/relation *)
let decl_of_fun id f =
  { FO_rel.
    decl_id=id;
    decl_arity=List.length f.fun_ty_args;
    decl_low=f.fun_low;
    decl_high=f.fun_high;
  }

type domain = {
  dom_ty: FO.Ty.t;
  dom_id: ID.t; (* ID corresponding to the type *)
  dom_su: FO_rel.sub_universe;
}

type state = {
  domain_size: int;
    (* size of domains *)
  mutable domains: domain TyTbl.t;
    (* atomic type -> domain *)
  funs: fun_ ID.Tbl.t;
    (* function -> relation *)
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

let find_fun_ state id : fun_ option = ID.Tbl.get state.funs id

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
          (* [pred a b c] becomes [c in (b · (a · pred))];
             here we remove the last argument *)
          let last, args = match List.rev l with
            | [] -> assert false
            | x :: l -> x, List.rev l
          in
          FO_rel.in_ last (app_fun_ f args)
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
  let fun_domain (args:FO_rel.sub_universe list) : FO_rel.tuple_set =
    List.map FO_rel.ts_all args
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
          let fun_ty_args = List.map (su_of_ty state) ty_args in
          let fun_low = empty_domain in
          let fun_high = fun_domain fun_ty_args in
          let f = {
            fun_is_pred=true;
            fun_ty_args;
            fun_low;
            fun_high;
          } in
          declare_fun state id f;
          None
        | FO.TyApp _ ->
          (* function: encode as relation whose last argument is the return value *)
          let fun_ty_args =
            List.map (su_of_ty state) ty_args @
              [su_of_ty state ty_ret]
          in
          let fun_low = empty_domain in
          let fun_high = fun_domain fun_ty_args in
          let f = {
            fun_is_pred=false;
            fun_ty_args;
            fun_low;
            fun_high;
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

(* TODO *)
let decode _state _m = assert false

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
  pipe_with ~decode ~print

