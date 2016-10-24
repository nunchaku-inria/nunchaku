
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Wrapper for TIP} *)

open Nunchaku

module A = Tip_ast
module UA = UntypedAST
module Loc = Location

type 'a or_error = ('a, string) CCResult.t

let section = Utils.Section.make "parse_tip"

let parse_lexbuf buf : A.statement list or_error =
  try Tip_parser.parse_list Tip_lexer.token buf |> CCResult.return
  with e -> CCResult.of_exn_trace e

let parse_file file =
  try
    CCIO.with_in file
      (fun ic ->
         let buf = Lexing.from_channel ic in
         Loc.set_file buf file;
         parse_lexbuf buf)
  with e -> CCResult.of_exn_trace e

let parse_stdin () =
  let buf = Lexing.from_channel stdin in
  parse_lexbuf buf

let conv_loc (loc:A.Loc.t): Loc.t =
  let {A.Loc.file; start_line; start_column; stop_line; stop_column} = loc in
  Loc.mk file start_line start_column stop_line stop_column

let rec conv_ty (ty:A.ty): UA.ty = match ty with
  | A.Ty_bool -> UA.ty_prop
  | A.Ty_arrow (args,ret) ->
    UA.ty_arrow_list (List.map conv_ty args) (conv_ty ret)
  | A.Ty_app (s, []) ->
    UA.var s (* var or const: let type inference decide *)
  | A.Ty_app (s, args) ->
    UA.app (UA.var s) (List.map conv_ty args)

let conv_var (v,ty) = v, Some (conv_ty ty)
let conv_vars = List.map conv_var

(* TODO: support "default" in matches (update main AST…) *)

let rec conv_term (t:A.term): UA.term = match t with
  | A.True -> UA.true_
  | A.False -> UA.false_
  | A.Const s ->
    (* const of variable: let type inference decide *)
    UA.var s
  | A.App (f,l) ->
    UA.app (UA.var f) (List.map conv_term l)
  | A.HO_app (a,b) ->
    UA.app (conv_term a) [conv_term b]
  | A.If (a,b,c) ->
    UA.ite (conv_term a)(conv_term b)(conv_term c)
  | A.Match (u,branches) ->
    let branches =
      List.map
        (function
          | A.Match_default _ ->
            Utils.not_implemented "does not support `default` in matches"
          | A.Match_case (c, vars, rhs) ->
            c, List.map (fun v->`Var v) vars, conv_term rhs)
        branches
    in
    UA.match_with (conv_term u) branches
  | A.Let (bindings,body) ->
    List.fold_right
      (fun (v,t) body -> UA.let_ v (conv_term t) body)
      bindings (conv_term body)
  | A.Fun (var,body) ->
    UA.fun_ (conv_var var) (conv_term body)
  | A.Eq (a,b) ->
    UA.eq (conv_term a)(conv_term b)
  | A.Imply (a,b) -> UA.imply (conv_term a)(conv_term b)
  | A.And l -> UA.and_ (List.map conv_term l)
  | A.Or l -> UA.or_ (List.map conv_term l)
  | A.Not a -> UA.not_  (conv_term a)
  | A.Forall (vars,body) ->
    let vars = conv_vars vars in
    UA.forall_list vars (conv_term body)
  | A.Exists (vars,body) ->
    let vars = conv_vars vars in
    UA.exists_list vars (conv_term body)
  | A.Cast (a,_) -> conv_term a

let conv_decl (d:A.ty A.fun_decl): string * UA.ty =
  let tyvars = d.A.fun_ty_vars in
  let ty_args = List.map conv_ty d.A.fun_args in
  let ty_ret = conv_ty d.A.fun_ret in
  let ty = UA.ty_forall_list tyvars (UA.ty_arrow_list ty_args ty_ret) in
  d.A.fun_name, ty

(* return [f, vars, ty_f] *)
let conv_def (d:A.typed_var A.fun_decl): string * UA.typed_var list * UA.ty =
  let tyvars = d.A.fun_ty_vars in
  let vars = List.map conv_var d.A.fun_args in
  let ty_args = List.map (CCFun.compose snd conv_ty) d.A.fun_args in
  let ty_ret = conv_ty d.A.fun_ret in
  let ty = UA.ty_forall_list tyvars (UA.ty_arrow_list ty_args ty_ret) in
  d.A.fun_name, List.map (fun v->v, Some UA.ty_type) tyvars @ vars, ty

let convert (st:A.statement): UA.statement list =
  Utils.debugf 3 "convert TIP statement@ @[%a@]" (fun k->k A.pp_stmt st);
  let loc = CCOpt.map conv_loc st.A.loc in
  match st.A.stmt with
    | A.Stmt_decl_sort (s,i) ->
      let ty = UA.ty_arrow_list (CCList.init i (fun _ -> UA.ty_type)) UA.ty_type in
      [UA.decl ?loc ~attrs:[] s ty]
    | A.Stmt_decl d ->
      let s, ty = conv_decl d in
      [UA.decl ?loc ~attrs:[] s ty]
    | A.Stmt_assert t ->
      let t = conv_term t in
      [UA.axiom ?loc [t]]
    | A.Stmt_assert_not (tyvars,g) ->
      (* goal *)
      let g = UA.ty_forall_list tyvars ?loc (conv_term g) in
      [UA.goal ?loc g]
    | A.Stmt_data (tyvars, l) ->
      let l = List.map
          (fun (id, cstors) ->
             let cstors =
               List.map
                 (fun c ->
                    let args = c.A.cstor_args |> List.map snd |> List.map conv_ty in
                    c.A.cstor_name, args)
                 cstors
             in
             (id, tyvars, cstors))
          l
      in
      [UA.data ?loc l]
    | A.Stmt_check_sat -> [] (* trivial *)
    | A.Stmt_fun_def fr
    | A.Stmt_fun_rec fr ->
      (* definition becomes a decl + universal axioms *)
      let f, vars, ty_f = conv_def fr.A.fr_decl in
      let vars_as_t =
        List.map (fun (s,_) -> UA.var s) vars
      in
      let body = conv_term fr.A.fr_body in
      let ax = UA.forall_list ?loc vars (UA.eq (UA.app (UA.var f) vars_as_t) body) in
      let def = UA.rec_ ?loc [f, ty_f, [ax]] in
      [def]
    | A.Stmt_funs_rec _
      ->
      assert false (* TODO *)

let convert_l ?(into=CCVector.create()) l =
  List.iter (fun st -> CCVector.append_list into (convert st)) l;
  into

(** {2 Parse + convert} *)

let parse ?mode:_ ?(into=CCVector.create()) src
  : UA.statement CCVector.vector or_error =
  let open CCResult.Infix in
  begin match src with
    | `Stdin -> parse_stdin ()
    | `File f -> parse_file f
  end >|= convert_l ~into
