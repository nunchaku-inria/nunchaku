
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lift Undefined} *)

open Nunchaku_core

module TI = TermInner
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module TyMo = TypeMono.Make(T)

let name = "lift_undefined"

let section = Utils.Section.make name
let error_ msg = failwith (Utils.err_sprintf "%s: %s" name msg)
let errorf_ fmt = CCFormat.ksprintf fmt ~f:error_

type term = T.t
type ty = T.t

type decode_state = {
  unknowns: unit ID.Tbl.t;
  (* set of all the unknowns lifted to toplevel *)
}

(** {2 Encoding} *)

type state = {
  new_decls: (ID.t * ty) CCVector.vector;
  (* new declarations *)
  tbl: ID.t U.Tbl.t;
  (* [unknown_(term) -> toplevel-id] *)
  env: (term, ty) Env.t;
  (* environment *)
  decode: decode_state;
  (* for decoding *)
}

let create_state ~env () : state = {
  env;
  tbl=U.Tbl.create 16;
  new_decls=CCVector.create();
  decode={unknowns=ID.Tbl.create 16};
}

let pop_decls state =
  let new_decls =
    CCVector.to_list state.new_decls
    |> List.rev_map
      (fun (id,ty) -> Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty)
  in
  CCVector.clear state.new_decls;
  new_decls

(* make a new "unknown" *)
let decl_new state (t:term) ty : ID.t =
  let id = ID.make (TyMo.mangle ~sep:"_" ty) in
  Utils.debugf ~section 5 "(@[declare_new %a:@ `@[%a@]`@])"
    (fun k->k ID.print id P.print ty);
  CCVector.push state.new_decls (id, ty);
  assert (not (U.Tbl.mem state.tbl t));
  U.Tbl.add state.tbl t id;
  ID.Tbl.add state.decode.unknowns id ();
  id

(* given [unknown_self t], find the arguments of the lifted version *)
let find_args (t:term): term list = match T.repr t with
  | TI.Const _ -> []
  | TI.App (_, l) -> l
  | _ ->
    errorf_ "cannot find type arguments for `undefined_self @[%a@]`" P.print t

(* recursive traversal of terms, lifting unknowns.
   We carry a substitution around so that the unknowns' arguments are
   path dependent.
   Example: [f x = match x with 0 -> ?1(f x) | s y -> ?2(f x) end]
   should become [f x = match x with 0 -> u1 | s y -> u2 y end]
   where [u1] is an undefined constant and [u2] an undefined function.
*)
let encode_term state ?(subst=Var.Subst.empty) t =
  let rec aux subst t = match T.repr t with
    | TI.Builtin (`Undefined_self t) ->
      (* find free variables of [t] *)
      let t = U.eval ~subst t in
      let args =
        find_args t
        |> U.free_vars_list
        |> U.VarSet.to_list
      in
      (* find or declare toplevel constant for this particular unknown *)
      let new_id = match U.Tbl.get state.tbl t with
        | Some new_id -> new_id
        | None ->
          (* declare new id *)
          let ty_args = List.map Var.ty args in
          let ty = U.ty_arrow_l ty_args (U.ty_exn ~env:state.env t) in
          decl_new state t ty
      in
      U.app_const new_id (List.map U.var args)
    | TI.Match (u, m, def) ->
      let u = aux subst u in
      let def = TI.map_default_case (aux subst) def in
      let m =
        ID.Map.mapi
          (fun c_id (vars,rhs) -> match T.repr u with
             | TI.Var v ->
               (* so we match [v] against the pattern [c_id vars],
                  therefore in [rhs] we can replace [v] by [c_id vars]. *)
               let subst =
                 Var.Subst.add ~subst v (U.app_const c_id (List.map U.var vars))
               in
               vars, aux subst rhs
             | _ -> vars, aux subst rhs)
          m
      in
      U.match_with u m ~def
    | _ ->
      U.map () t ~bind:(fun () v->(),v) ~f:(fun () -> aux subst)
  in
  aux subst t

let encode_stmt state stmt =
  let stmt' = Stmt.map stmt ~ty:(fun t->t) ~term:(encode_term state) in
  let new_decls = pop_decls state in
  new_decls @ [stmt']

let encode_pb pb =
  let env = Problem.env pb in
  let state = create_state ~env () in
  let pb' =
    Problem.flat_map_statements pb ~f:(encode_stmt state)
  in
  pb', state.decode



(** {2 Decoding} *)

(* remove from model the values of unknowns *)
let decode_model (state:decode_state) m =
  Model.filter m
    ~values:(fun (t,_,_) -> match T.repr t with
      | TI.Const id -> not (ID.Tbl.mem state.unknowns id)
      | _ -> true)

(** {2 Plumbing} *)

let pipe ~print ~check =
  let on_encoded =
    Utils.singleton_if print () ~f:(fun () ->
      let module Ppb = Problem.Print(P)(P) in
      Format.printf "@[<v2>@{<Yellow>after %s@}:@ %a@]@." name Ppb.print)
    @
    Utils.singleton_if check () ~f:(fun () ->
      let module C = TypeCheck.Make(T) in
      C.empty () |> C.check_problem)
  in
  let decode st = Problem.Res.map_m ~f:(decode_model st) in
  Transform.make
    ~name
    ~input_spec:Transform.Features.(of_list [Ty, Mono])
    ~map_spec:(fun s->s)
    ~on_encoded
    ~encode:encode_pb
    ~decode
    ()


