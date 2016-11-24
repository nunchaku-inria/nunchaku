
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lambda Lifting} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P

let name = "lambda_lift"
let section = Utils.Section.make name

type term = T.t
type ty = T.t

(* term -> 'a, modulo alpha equivalence *)
module TermTbl = CCHashtbl.Make(struct
  type t = T.t
  let equal = U.equal
  let hash = U.hash_alpha_eq
  end)

type state = {
  mutable count: int;
    (* counter for new names *)
  mutable env: (T.t,ty) Env.t;
    (* signature *)
  funs: T.t TermTbl.t;
    (* function -> lambda-lifted function *)
  new_ids: unit ID.Tbl.t;
    (* set of newly introduced functions *)
}

let create_state ~env () =
  { count=0;
    env;
    funs=TermTbl.create 16;
    new_ids=ID.Tbl.create 16;
  }

let fresh_fun_ ~state =
  let new_fun = ID.make (Printf.sprintf "anon_fun_%d" state.count) in
  state.count <- state.count + 1;
  new_fun

(* are we in a recursive/spec block? If yes, the ID set is the set of
   IDs being declared *)
type in_scope_of =
  | In_nothing
  | In_rec of
      ID.Set.t * (* ids locally declared *)
      (T.t, T.t) Stmt.rec_def list ref (* new definitions *)
  | In_spec of
      ID.Set.t *
      (ID.t * ty * term) list ref (* new axioms *)

(* state for declaring the lambda lifted functions *)
type local_state = {
  new_decls: (term, ty) Stmt.t CCVector.vector;
    (* toplevel statements to be added to the problem *)
  mutable in_scope : in_scope_of;
    (* if [local_ids] is not empty, we are in scope of "rec" or "spec" declarations *)
}

(* does [t] contain any ID of [set]? *)
let contains_some_id ~of_:set t =
  U.to_seq t
  |> Sequence.exists
    (fun t' -> match T.repr t' with
       | TI.Const id -> ID.Set.mem id set
       | _ -> false)

(* declare new function [f : ty := fun vars. body] *)
let mk_new_rec f ty vars body =
  let eqns = Stmt.Eqn_single (vars, body) in
  let defined = Stmt.mk_defined ~attrs:[] f ty in
  {Stmt.
    rec_ty_vars=vars;
    rec_defined=defined;
    rec_eqns=eqns;
  }

let mk_axiom f vars body =
  U.forall_l vars (U.eq (U.app (U.const f) (List.map U.var vars)) body)

let declare_new_rec f ty vars body =
  let def = mk_new_rec f ty vars body in
  Stmt.axiom_rec ~info:Stmt.info_default [def]

(* TODO: expand `let` if its parameter is HO, and
   compute WHNF in case [var args] (new β redexes) *)

let find_ty_ ~state t =
  U.ty_exn ~sigma:(Env.find_ty ~env:state.env) t

let decl_fun_ ~state ~attrs id ty =
  state.env <- Env.declare ~attrs ~env:state.env id ty

let is_lambda_ t = match T.repr t with
  | TI.Bind (`Fun, _, _) -> true
  | _ -> false

(* given two lists of variables, return:
   - a list of fresh variables that is a copy of the longest one
   - a substitution that renames l1 and l2 to those new variables
   - the suffixes to add to [l1] (resp. l2) so that they have
     the same length as the list of fresh variables
  precond: variables in the common prefix of l1 and l2 have compatible types *)
let complete_vars ~subst l1 l2 =
  let rec aux vars args1 args2 subst l1 l2 = match l1, l2 with
    | [], [] -> List.rev vars, List.rev args1, List.rev args2, subst
    | [], v::tail ->
      let v' = Var.fresh_copy v in
      let subst = Var.Subst.add ~subst v v' in
      let args1 = U.var v'::args1 in
      aux (v'::vars) args1 args2 subst [] tail
    | v::tail, [] ->
      let v' = Var.fresh_copy v in
      let subst = Var.Subst.add ~subst v v' in
      let args2 = U.var v' :: args2 in
      aux (v'::vars) args1 args2 subst tail []
    | v1::tail1, v2::tail2 ->
      let v' = Var.fresh_copy v1 in
      let subst = Var.Subst.add ~subst v1 v' in
      let subst = Var.Subst.add ~subst v2 v' in
      aux (v'::vars) args1 args2 subst tail1 tail2
  in
  aux [] [] [] subst l1 l2

(* traverse [t] recursively, replacing lambda terms by new named functions *)
let rec tr_term ~state local_state subst t = match T.repr t with
  | TI.Var v -> U.var (Var.Subst.find_or ~default:v ~subst v)
  | TI.Bind (`Fun, _, _) when TermTbl.mem state.funs t ->
      (* will only work if [t] is alpha-equivalent to [t']; in particular
         that implies that [t] and [t'] capture exactly the same terms,
         which makes this safe *)
      let t' = TermTbl.find state.funs t in
      Utils.debugf ~section 5 "@[<2>re-use `@[%a@]`@ for `@[%a@]`@]"
        (fun k->k P.print t' P.print t);
      t'
  | TI.Bind (`Fun, v, body) ->
      (* first, λ-lift in the body *)
      let body = tr_term ~state local_state subst body in
      (* captured variables *)
      let captured_vars =
        U.free_vars ~bound:(U.VarSet.singleton v) body
        |> U.VarSet.to_list
      in
      (* compute type of new function *)
      let _, body_ty_args, ty_ret = find_ty_ ~state body |> U.ty_unfold in
      let ty =
        U.ty_arrow_l
          (List.map Var.ty captured_vars @ Var.ty v :: body_ty_args)
          ty_ret in
      (* fully apply body *)
      let body_vars =
        List.mapi (fun i ty -> Var.makef ~ty "eta_%d" i) body_ty_args
      in
      let body = U.app body (List.map U.var body_vars) in
      (* declare new toplevel function *)
      let new_fun = fresh_fun_ ~state in
      let new_vars = captured_vars @ v :: body_vars in
      (* declare new function *)
      decl_fun_ ~state ~attrs:[] new_fun ty;
      Utils.debugf ~section 5 "@[<2>declare `@[%a : %a@]`@ for `@[%a@]`@]"
        (fun k->k ID.print new_fun P.print ty P.print t);
      (* how we define [new_fun] depends on whether it is mutually recursive
         with the surrounding rec/spec *)
      begin match local_state.in_scope with
        | In_rec (ids, l) when contains_some_id ~of_:ids body ->
            (* body needs to be mutually recursive with [ids], and is a rec *)
            let def = mk_new_rec new_fun ty new_vars body in
            l := def :: !l
        | In_spec (ids, l) when contains_some_id ~of_:ids body ->
            (* body needs to be mutually recursive with [ids], and is a spec *)
            let ax = mk_axiom new_fun new_vars body in
            l := (new_fun, ty, ax) :: !l
        | In_rec _
        | In_spec _
        | In_nothing ->
            (* no mutual dependencies, can emit toplevel "rec" *)
            let decl = declare_new_rec new_fun ty new_vars body in
            CCVector.push local_state.new_decls decl;
      end;
      (* replace [fun v. body] by [new_fun vars] *)
      let t' = U.app_const new_fun (List.map U.var captured_vars) in
      TermTbl.add state.funs t t'; (* save it *)
      ID.Tbl.add state.new_ids new_fun ();
      t'
  | TI.Builtin (`Eq (a,b)) when is_lambda_ a || is_lambda_ b ->
      (* extensionality: [(λx. t) = f] becomes [∀x. t = t' x] *)
      let vars1, body1 = U.fun_unfold a in
      let vars2, body2 = U.fun_unfold b in
      let new_vars, args1, args2, subst = complete_vars ~subst vars1 vars2 in
      let body1 = tr_term ~state local_state subst (U.app body1 args1) in
      let body2 = tr_term ~state local_state subst (U.app body2 args2) in
      (* quantify on common variables *)
      U.forall_l new_vars (U.eq body1 body2)
  | _ ->
    U.map subst t
      ~bind:Var.Subst.rename_var
      ~f:(fun subst -> tr_term ~state local_state subst)

let tr_problem pb =
  let env = Problem.env pb in
  let state = create_state ~env () in
  let local_state = {
    new_decls = CCVector.create ();
    in_scope = In_nothing;
  } in
  let pb' =
    Problem.flat_map_statements pb
    ~f:(fun stmt ->
      let info = Stmt.info stmt in
      let stmt' = match Stmt.view stmt with
        | Stmt.Axiom (Stmt.Axiom_rec defs) ->
            (* caution, some lambda lifted function might depend on
               the recursive block *)
            let ids =
              Stmt.defined_of_recs defs
              |> Sequence.map Stmt.id_of_defined
              |> ID.Set.of_seq
            in
            let l = ref [] in
            local_state.in_scope <- In_rec (ids, l);
            let defs' = Stmt.map_rec_defs defs
                ~ty:CCFun.id ~term:(tr_term ~state local_state Var.Subst.empty)
            in
            (* combine [defs'] with additional definitions in [l] *)
            let new_defs = List.rev_append !l defs' in
            Stmt.axiom_rec ~info new_defs
        | Stmt.Axiom (Stmt.Axiom_spec spec) ->
            (* caution, some lambda lifted function might depend on
               the recursive block *)
            let ids =
              Stmt.defined_of_spec spec
              |> Sequence.map Stmt.id_of_defined
              |> ID.Set.of_seq
            in
            let l = ref [] in
            local_state.in_scope <- In_spec (ids, l);
            let spec' = Stmt.map_spec_defs spec
                ~ty:CCFun.id ~term:(tr_term ~state local_state Var.Subst.empty)
            in
            let new_defined, new_axioms =
              List.map (fun (id,ty,ax) -> Stmt.mk_defined ~attrs:[] id ty, ax) !l
              |> List.split
            in
            (* combine [defs'] with additional definitions in [l] *)
            let new_defs =
              { spec' with Stmt.
                spec_defined = new_defined @ spec'.Stmt.spec_defined;
                spec_axioms = new_axioms @ spec'.Stmt.spec_axioms;
              }
            in
            Stmt.axiom_spec ~info new_defs
        | _ ->
            local_state.in_scope <- In_nothing;
            Stmt.map stmt ~ty:CCFun.id
              ~term:(tr_term ~state local_state Var.Subst.empty)
      in
      (* append auxiliary definitions *)
      let res =
        CCVector.to_list local_state.new_decls
        @ [stmt']
      in
      CCVector.clear local_state.new_decls;
      res)
  in
  pb', state

let decode_model ~state m =
  Model.filter m
    ~values:(fun (t,_,_) -> match T.repr t with
      | TI.Const id when ID.Tbl.mem state.new_ids id ->
        false (* drop anonymous funs from model *)
      | _ -> true)

let pipe_with ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print ()
      ~f:(fun () ->
        let module Ppb = Problem.Print(P)(P) in
        Format.printf "@[<v2>@{<Yellow>after λ-lifting@}: %a@]@." Ppb.print)
    @
    Utils.singleton_if check ()
      ~f:(fun () ->
         let module C = TypeCheck.Make(T) in
         C.empty() |> C.check_problem)
  in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list
          [Ty, Mono; Ind_preds, Absent; Eqn, Eqn_single])
    ~map_spec:Transform.Features.(update Fun Absent)
    ~on_encoded
    ~encode:tr_problem
    ~decode
    ()

let pipe ~print ~check =
  pipe_with ~check ~print
    ~decode:(fun state -> Problem.Res.map_m ~f:(decode_model ~state))

