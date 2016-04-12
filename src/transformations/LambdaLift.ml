
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lambda Lifting} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement

type inv = <ty:[`Mono]; ind_preds:[`Absent]; eqn:[`Single]>

let name = "lambda_lift"

module Make(T : TI.S) = struct
  module T = T
  module U = TI.Util(T)
  module P = TI.Print(T)

  type term = T.t
  type ty = T.t

  type state = {
    mutable count: int;
      (* counter for new names *)
    sigma: ty Signature.t;
      (* signature *)
  }
  (* TODO: store information for decoding *)

  let create_state ~sigma () =
    { count=0; sigma; }

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
        (T.t, T.t, inv) Stmt.rec_def list ref (* new definitions *)
    | In_spec of
        ID.Set.t *
        (ID.t * ty * term) list ref (* new axioms *)

  (* state for declaring the lambda lifted functions *)
  type local_state = {
    new_decls: (term, ty, inv) Stmt.t CCVector.vector;
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
  let mk_new_rec kind f ty vars body =
    let eqns = Stmt.Eqn_single (vars, body) in
    let defined = Stmt.mk_defined f ty in
    {Stmt.
      rec_vars=vars;
      rec_defined=defined;
      rec_kind=kind;
      rec_eqns=eqns;
    }

  let mk_axiom f vars body =
    U.forall_l vars (U.eq (U.app (U.const f) (List.map U.var vars)) body)

  let declare_new_rec kind f ty vars body =
    let def = mk_new_rec kind f ty vars body in
    Stmt.axiom_rec ~info:Stmt.info_default [def]

  (* TODO: expand `let` if its parameter is HO, and
     compute WHNF in case [var args] (new β redexes) *)

  (* traverse [t] recursively, replacing lambda terms by new named functions *)
  let rec tr_term ~state local_state t = match T.repr t with
    | TI.Bind (`Fun, v, body) ->
        (* first, λ-lift in the body *)
        let body = tr_term ~state local_state body in
        (* captured variables *)
        let captured_vars =
          U.free_vars ~bound:(U.VarSet.singleton v) body
          |> U.VarSet.to_list
        in
        (* compute type of new function *)
        let ty_ret =
          U.ty_exn ~sigma:(Signature.find ~sigma:state.sigma) body in
        let ty = U.ty_arrow_l (List.map Var.ty captured_vars @ [Var.ty v]) ty_ret in
        let kind = if U.ty_is_Prop ty_ret then Stmt.Decl_prop else Stmt.Decl_fun in
        (* declare new toplevel function *)
        let new_fun = fresh_fun_ ~state in
        let new_vars = captured_vars @ [v] in
        (* how we define [new_fun] depends on whether it is mutually recursive
           with the surrounding rec/spec *)
        begin match local_state.in_scope with
          | In_rec (ids, l) when contains_some_id ~of_:ids body ->
              (* body needs to be mutually recursive with [ids], and is a rec *)
              let def = mk_new_rec kind new_fun ty new_vars body in
              l := def :: !l
          | In_spec (ids, l) when contains_some_id ~of_:ids body ->
              (* body needs to be mutually recursive with [ids], and is a spec *)
              let ax = mk_axiom new_fun new_vars body in
              l := (new_fun, ty, ax) :: !l
          | In_rec _
          | In_spec _
          | In_nothing ->
              (* no mutual dependencies, can emit toplevel "rec" *)
              let decl = declare_new_rec kind new_fun ty new_vars body in
              CCVector.push local_state.new_decls decl;
        end;
        (* replace [fun v. body] by [new_fun vars] *)
        U.app (U.const new_fun) (List.map U.var captured_vars)
    | _ -> tr_term' ~state local_state t
  and tr_term' ~state new_decls t =
    U.map () t ~bind:(fun () v -> (), v) ~f:(fun () -> tr_term ~state new_decls)

  let tr_problem pb =
    let sigma = Problem.signature pb in
    let state = create_state ~sigma () in
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
                  ~ty:CCFun.id ~term:(tr_term ~state local_state)
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
                  ~ty:CCFun.id ~term:(tr_term ~state local_state)
              in
              let new_defined, new_axioms =
                List.map (fun (id,ty,ax) -> Stmt.mk_defined id ty, ax) !l
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
              Stmt.map stmt ~ty:CCFun.id ~term:(tr_term ~state local_state)
        in
        (* append auxiliary definitions *)
        let res =
          CCVector.to_list local_state.new_decls
          |> CCList.cons stmt'
          |> List.rev
        in
        CCVector.clear local_state.new_decls;
        res)
    in
    pb', state

  (* TODO *)
  let decode_model ~state:_ m = m

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
           C.check_problem ?env:None)
    in
    Transform.make1
      ~name
      ~on_encoded
      ~encode:tr_problem
      ~decode
      ()

  let pipe ~print ~check =
    pipe_with ~check ~decode:(fun state m -> decode_model ~state m) ~print
end

