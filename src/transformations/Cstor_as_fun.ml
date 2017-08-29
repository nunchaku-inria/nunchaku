

(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Functions for Partially Applied Constructors} *)

open Nunchaku_core

module Stmt = Statement
module TI = TermInner
module T = TermInner.Default
module P = T.P
module U = T.U
module PStmt = Stmt.Print(P)(P)

let name = "cstor_as_fun"
let long_name = "removal of partially applied constructors"
let section = Utils.Section.make name

type ty = TermInner.Default.t
type term = TermInner.Default.t
type var = ty Var.t
type env = (term,term) Env.t

type state = {
  cstor_funs_map: ID.t ID.Tbl.t;
  (* constructors-as-functions, for partial applications *)
  cstor_funs_set: unit ID.Tbl.t;
  (* set of constructors-as-functions introduced so far*)
}

let create() = {
  cstor_funs_map=ID.Tbl.create 16;
  cstor_funs_set=ID.Tbl.create 16;
}

let is_defined_fun st id = ID.Tbl.mem st.cstor_funs_set id

type def = ty Statement.defined * var list * term
(** The definition of a term *)

(* get-or-define a rec-function that simulates the given constructor [id],
   when [id] is partially applied (making it impossible to add guards
   on its).
   If [f] simulates [id], it means:
   [f x1…xn = cstor x1…xn
     asserting (is-cstor (f x1…xn)
      ∧ ∀i. selector-cstor-i (f x1…xn) = xi)]
*)
let cstor_as_fun (state:state) (id:ID.t) ~ty : ID.t * def option =
  try ID.Tbl.find state.cstor_funs_map id, None
  with Not_found ->
    let f_id = ID.make_f "%s-as-fun" (ID.name id) in
    Utils.debugf ~section 3
      "@[<2>introduce `@[%a : %a@]`@ for partial application of `%a`@]"
      (fun k->k ID.pp f_id P.pp ty ID.pp id);
    let f_defined = Stmt.mk_defined ~attrs:[] f_id ty in
    (* define [f] by building a statement *)
    let _l, ty_args, _ = U.ty_unfold ty in
    assert (_l=[]);
    let vars = List.mapi (fun i ty -> Var.makef ~ty "x_%d" i) ty_args in
    let vars_t = List.map U.var vars in
    (* [id x1…xn] *)
    let t = U.app_const id vars_t in
    Utils.debugf ~section 5 "add new def `%a`"
      (fun k->
         let st =
           Stmt.axiom_rec ~info:Stmt.info_default
             [ { Stmt.rec_defined=f_defined; rec_ty_vars=[];
                 rec_eqns=Stmt.Eqn_single (vars, t); } ] in
         k PStmt.pp st);
    ID.Tbl.add state.cstor_funs_map id f_id;
    ID.Tbl.add state.cstor_funs_set f_id ();
    f_id, Some (f_defined, vars, t)

(** {2 Global interface} *)

type glob_state = {
  state: state;
  mutable env: env;
  mutable new_stmts : (term, ty) Stmt.t CCVector.vector;
  (* used for new declarations. [id, type, attribute list] *)
}

let get_cstor_as_fun (gst:glob_state) id ty : ID.t =
  let f_id, f_stmt = cstor_as_fun gst.state id ~ty in
  (* declare statement to define [f_id]? *)
  begin match f_stmt with
    | None -> ()
    | Some (f_defined,vars,rhs) ->
      let stmt =
        Stmt.axiom_rec ~info:Stmt.info_default
          [ { Stmt.rec_defined=f_defined; rec_ty_vars=[];
              rec_eqns=Stmt.Eqn_single (vars, rhs); } ]
      in
      CCVector.push gst.new_stmts stmt;
      gst.env <- Env.add_statement ~env:gst.env stmt;
  end;
  f_id

let encode_term (gst:glob_state) (t:term) : term =
  let rec aux t = match T.repr t with
    | TI.Const id ->
      let info = Env.find_exn ~env:gst.env id in
      if Env.is_cstor info && U.ty_arity info.Env.ty > 0 then (
        let f_id = get_cstor_as_fun gst id info.Env.ty in
        U.const f_id
      ) else t
    | TI.App (f, l) ->
      let l = List.map aux l in
      begin match T.repr f with
        | TI.Const id ->
          let info = Env.find_exn ~env:gst.env id in
          if Env.is_cstor info && U.ty_arity info.Env.ty > List.length l then (
            (* partially applied cstor *)
            let f_id = get_cstor_as_fun gst id info.Env.ty in
            U.app_const f_id l
          ) else U.app f l
        | _ ->
          let f = aux f in
          U.app f l
      end
    | _ -> U.map ~bind:(fun () v -> (), v) ~f:(fun () -> aux) () t
  in
  aux t

let encode_stmt (gst:glob_state) stmt : (_,_) Statement.t =
  Stmt.map stmt ~ty:CCFun.id ~term:(encode_term gst)

let encode_pb (pb:(term,ty) Problem.t) : (_,_) Problem.t * state =
  let env = Problem.env pb in
  let gst = {
    env;
    state=create();
    new_stmts=CCVector.create()
  } in
  let pb' =
    Problem.flat_map_statements pb
      ~f:(fun stmt ->
        let stmt' = encode_stmt gst stmt in
        let prelude = CCVector.to_list gst.new_stmts in
        CCVector.clear gst.new_stmts;
        prelude @ [stmt']
      )
  in
  pb', gst.state

let decode_model state m : (_,_) Model.t =
  Model.filter m
    ~values:(fun (t,_,_) -> match T.repr t with
      | TI.Const id when is_defined_fun state id -> false
      | _ -> true)

(** {2 Pipe} *)

let pipe_with ?on_decoded ~decode ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module PPb = Problem.Print(P)(P) in
      Format.printf
        "@[<v2>@{<Yellow>after %s@}: %a@]@." long_name PPb.pp)
    @
      Utils.singleton_if check () ~f:(fun () ->
        let module C = TypeCheck.Make(T) in
        C.empty () |> C.check_problem)
  in
  Transform.make
    ?on_decoded
    ~on_encoded
    ~input_spec:Transform.Features.(of_list
          [Ty, Mono; Partial_app_cstor, Present])
    ~map_spec:Transform.Features.(update_l [Partial_app_cstor, Absent])
    ~name
    ~encode:(fun p -> encode_pb p)
    ~decode
    ()

let pipe ~print ~check =
  let on_decoded = if print
    then
      [Format.printf "@[<2>@{<Yellow>res %s@}:@ %a@]@."
         long_name (Problem.Res.pp P.pp' P.pp)]
    else []
  in
  let decode state = Problem.Res.map_m ~f:(decode_model state) in
  pipe_with ~on_decoded ~print ~decode ~check
