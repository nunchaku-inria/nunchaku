
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 FOL to Relational FO Logic} *)

open Nunchaku_core

let name = "fo_to_rel"

type problem1 = (FO.T.t, FO.Ty.t) FO.Problem.t
type model1 = (FO.T.t, FO.Ty.t) Model.t

type problem2 = FO_rel.problem
type model2 = (FO_rel.expr, FO_rel.expr) Model.t

let section = Utils.Section.(make ~parent:root) name

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "in %s: %s" name msg)
      | _ -> None)

let error msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf ~f:error msg

(** {2 Encoding} *)

type tuple = ID.t list

type fun_ = {
  fun_ty_args: ID.Set.t list;
  fun_low: tuple list;
  fun_high: tuple list;
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

type state = {
  domain_size: int;
    (* size of domains *)
  domains: ID.Set.t ID.Tbl.t;
    (* atomic type -> domain *)
  mutable univ: ID.Set.t;
    (* the whoooooole universe *)
  true_: ID.t;
    (* "true" constant *)
  funs: fun_ ID.Tbl.t;
    (* function -> relation *)
}

let create_state ~size () =
  let true_ = ID.make "true_" in
  let state = {
    domain_size=size;
    domains=ID.Tbl.create 16;
    univ=ID.Set.singleton true_;
    true_;
    funs=ID.Tbl.create 16;
  } in
  (* declare [true] *)
  ID.Tbl.add state.funs true_
    { fun_ty_args=[];
      fun_low=[[true_]];
      fun_high=[[true_]];
      fun_is_pred=true;
    };
  state

(* ensure the type is declared *)
let declare_ty state id =
  if ID.Tbl.mem state.domains id then errorf "type %a declared twice" ID.print id;
  (* TODO: handle cardinality constraints *)
  let set =
    CCList.init state.domain_size
      (fun i -> ID.make_f "%a_%d" ID.print_name id i)
    |> ID.Set.of_list
  in
  Utils.debugf ~section 3 "@[<2>declare type %a@ = {@[%a@]}@]"
    (fun k->k ID.print id FO_rel.print_set set);
  ID.Tbl.add state.domains id set

let domain_of_ty_id state id = ID.Tbl.find state.domains id

(* type -> its domain *)
let domain_of_ty state ty =
  match FO.Ty.view ty with
    | FO.TyApp (id,[]) ->
      domain_of_ty_id state id
    | FO.TyApp (_, _::_) -> assert false (* TODO *)
    | FO.TyBuiltin `Prop ->
      ID.Set.singleton state.true_

let declare_fun state id f =
  Utils.debugf ~section 3 "@[<2>declare function@ `@[%a@]`@]"
    (fun k->k FO_rel.print_decl (decl_of_fun id f));
  ID.Tbl.add state.funs id f

let ty_is_declared state id = ID.Tbl.mem state.domains id
let fun_is_declared state id = ID.Tbl.mem state.funs id

(* apply relation to list of arguments *)
let rec app_ f l = match l with
  | [] -> f
  | x :: tail -> app_ (FO_rel.join x f) tail

(* term -> expr *)
let rec encode_term state t : FO_rel.expr =
  match FO.T.view t with
    | FO.Builtin _ -> assert false (* TODO *)
    | FO.Var v -> FO_rel.var (encode_var state v)
    | FO.App (f,l) ->
      if not (fun_is_declared state f)
      then errorf "function %a is undeclared" ID.print f;
      let f = FO_rel.const f in
      let l = List.map (encode_term state) l in
      app_ f l
    | FO.DataTest (_,_)
    | FO.DataSelect (_,_,_) ->
      error "should have eliminated data{test/select} earlier"
    | FO.Undefined (_,_) -> assert false (* TODO? *)
    | FO.Fun (_,_) ->
      errorf "cannot translate function `@[%a@]` to FO_rel" FO.print_term t
    | FO.Let (_,_,_) -> assert false (* TODO: expand *)
    | FO.Ite (_,_,_) -> assert false (* TODO: *)
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
      (* double inclusion *)
      let a = encode_term state a in
      let b = encode_term state b in
      FO_rel.and_ (FO_rel.in_ a b) (FO_rel.in_ b a)
    | FO.True -> FO_rel.some (FO_rel.const state.true_)
    | FO.False -> FO_rel.no (FO_rel.const state.true_)
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
    | FO.Builtin _
    | FO.Var _
    | FO.Mu (_,_)
    | FO.Unparsable _
    | FO.DataTest (_,_)
    | FO.DataSelect (_,_,_)
    | FO.Undefined (_,_)
    | FO.Fun (_,_)
    | FO.App _ ->
      (* atomic formula *)
      FO_rel.some (encode_term state t)

and encode_var state v =
  Var.update_ty v ~f:(encode_ty state)

and encode_ty state ty : FO_rel.expr =
  match FO.Ty.view ty with
    | FO.TyBuiltin `Prop -> assert false
    | FO.TyApp (id, []) ->
      assert (ty_is_declared state id);
      FO_rel.const id
    | FO.TyApp (_, _::_) -> assert false (* TODO *)

(* cartesian product of list of sets *)
let rec product_l = function
  | [] -> [[]]
  | s :: tail ->
    let tuples = product_l tail in
    ID.Set.fold
      (fun id acc ->
         let l = List.rev_map (fun tup -> id::tup) tuples in
         List.rev_append l acc)
      s []

let encode_statement state st =
  match st with
    | FO.TyDecl (id,0) ->
      assert (not (ty_is_declared state id));
      declare_ty state id;
      None
    | FO.TyDecl (_, _) -> assert false (* TODO?? *)
    | FO.Decl (id, (ty_args, ty_ret)) ->
      assert (not (fun_is_declared state id));
      (* encoding differs for relations and functions *)
      begin match FO.Ty.view ty_ret with
        | FO.TyBuiltin `Prop ->
          (* encode predicate as itself *)
          let fun_ty_args = List.map (domain_of_ty state) ty_args in
          let fun_low = [] in
          let fun_high = product_l fun_ty_args in
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
            List.map (domain_of_ty state) ty_args @
              [domain_of_ty state ty_ret]
          in
          let fun_low = [] in
          let fun_high = product_l fun_ty_args in
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
                (fun i ty -> Var.make_f ~ty:(encode_ty state ty) "x_%d" i)
                ty_args
            in
            FO_rel.for_all_l vars
              (FO_rel.one
                 (app_ (FO_rel.const id) (List.map FO_rel.var vars)))
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
    |> FO_rel.and_l
  in
  (* extract declarations *)
  let decls =
    ID.Tbl.to_seq state.funs
    |> Sequence.map (CCFun.uncurry decl_of_fun)
    |> CCVector.of_seq ?init:None
    |> CCVector.freeze
  in
  let pb' = {
    FO_rel.
    pb_meta=FO.Problem.meta pb;
    pb_univ=state.univ;
    pb_decls=decls;
    pb_goal=form;
  } in
  pb', state

(** {2 Decoding} *)

let decode _state _m = assert false

(** {2 Pipes} *)

let pipe_with ~decode ~print =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      Format.printf "@[<2>@{<Yellow>after %s@}:@ %a@]@."
        name FO_rel.print_problem)
  in
  Transform.make ~name ~on_encoded ~encode:encode_pb ~decode ()

let pipe ~print =
  pipe_with ~decode ~print

