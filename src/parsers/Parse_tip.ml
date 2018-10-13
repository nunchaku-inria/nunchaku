
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Wrapper for TIP} *)

open Nunchaku_core

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

let rec conv_ty (ty:A.ty): UA.ty =
  let loc = Loc.get_loc ty in
  match Loc.get ty with
  | A.Ty_bool -> UA.ty_prop
  | A.Ty_arrow (args,ret) ->
    UA.ty_arrow_list ~loc (List.map conv_ty args) (conv_ty ret)
  | A.Ty_app (s, []) ->
    UA.var ~loc s (* var or const: let type inference decide *)
  | A.Ty_app (s, args) ->
    UA.app ~loc (UA.var ~loc s) (List.map conv_ty args)

let conv_var (v,ty) = v, Some (conv_ty ty)
let conv_vars = List.map conv_var

let rec conv_term (t:A.term): UA.term =
  let loc = A.t_loc t in
  match A.t_view t with
  | A.True -> UA.true_ ~loc
  | A.False -> UA.false_ ~loc
  | A.Const s ->
    (* const of variable: let type inference decide *)
    UA.var ~loc s
  | A.App (f,l) ->
    UA.app ~loc (UA.var ~loc f) (List.map conv_term l)
  | A.HO_app (a,b) ->
    UA.app ~loc (conv_term a) [conv_term b]
  | A.Distinct l ->
    List.map conv_term l
    |> CCList.diagonal
    |> List.map (fun (a,b) -> UA.neq ~loc a b)
    |> UA.and_ ~loc
  | A.If (a,b,c) ->
    UA.ite ~loc (conv_term a)(conv_term b)(conv_term c)
  | A.Match (u,branches) ->
    let def = ref None in
    let branches =
      CCList.filter_map
        (function
          | A.Match_default rhs ->
            begin match !def with
              | Some _ ->
                failwith "TIP parser: cannot have two `default` cases in the same match"
              | None -> def := Some (conv_term rhs)
            end;
            None
          | A.Match_case (c, vars, rhs) ->
            Some (c, List.map (fun v->`Var v) vars, conv_term rhs))
        branches
    in
    UA.match_with ~loc (conv_term u) branches ?default:!def
  | A.Let (bindings,body) ->
    List.fold_right
      (fun (v,t) body -> UA.let_ ~loc v (conv_term t) body)
      bindings (conv_term body)
  | A.Fun (var,body) ->
    UA.fun_ ~loc (conv_var var) (conv_term body)
  | A.Eq (a,b) ->
    UA.eq ~loc (conv_term a)(conv_term b)
  | A.Imply (a,b) -> UA.imply ~loc (conv_term a)(conv_term b)
  | A.And l -> UA.and_ ~loc (List.map conv_term l)
  | A.Or l -> UA.or_ ~loc (List.map conv_term l)
  | A.Not a -> UA.not_  ~loc (conv_term a)
  | A.Forall (vars,body) ->
    let vars = conv_vars vars in
    UA.forall_list ~loc vars (conv_term body)
  | A.Exists (vars,body) ->
    let vars = conv_vars vars in
    UA.exists_list ~loc vars (conv_term body)
  | A.Cast (a,_) -> conv_term a

let convert_term = conv_term
let convert_ty = conv_ty

let conv_decl (d:A.ty A.fun_decl): string * UA.ty =
  let loc = d.A.fun_loc in
  let tyvars = d.A.fun_ty_vars in
  let ty_args = List.map conv_ty d.A.fun_args in
  let ty_ret = conv_ty d.A.fun_ret in
  let ty = UA.ty_forall_list ~loc tyvars (UA.ty_arrow_list ~loc ty_args ty_ret) in
  d.A.fun_name, ty

(* return [f, vars, ty_f] *)
let conv_def (d:A.typed_var A.fun_decl): string * UA.typed_var list * UA.ty =
  let loc = d.A.fun_loc in
  let tyvars = d.A.fun_ty_vars in
  let vars = List.map conv_var d.A.fun_args in
  let ty_args = List.map (CCFun.compose snd conv_ty) d.A.fun_args in
  let ty_ret = conv_ty d.A.fun_ret in
  let ty = UA.ty_forall_list ~loc tyvars (UA.ty_arrow_list ~loc ty_args ty_ret) in
  d.A.fun_name, List.map (fun v->v, Some UA.ty_type) tyvars @ vars, ty

let convert_st (st:A.statement): UA.statement list =
  Utils.debugf 3 "convert TIP statement@ @[%a@]" (fun k->k A.pp_stmt st);
  let loc = conv_loc st.A.loc in
  match st.A.stmt with
    | A.Stmt_decl_sort (s,i) ->
      let ty = UA.ty_arrow_list ~loc (CCList.init i (fun _ -> UA.ty_type)) UA.ty_type in
      [UA.decl ~loc ~attrs:[] s ty]
    | A.Stmt_decl d ->
      let s, ty = conv_decl d in
      [UA.decl ~loc ~attrs:[] s ty]
    | A.Stmt_assert t ->
      let t = conv_term t in
      [UA.axiom ~loc [t]]
    | A.Stmt_assert_not (tyvars,g) ->
      (* goal *)
      let g = UA.ty_forall_list tyvars ~loc (conv_term g) in
      [UA.goal ~loc (UA.not_ ~loc g)]
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
      [UA.data ~loc l]
    | A.Stmt_check_sat -> [] (* trivial *)
    | A.Stmt_fun_def fr
    | A.Stmt_fun_rec fr ->
      let loc = fr.A.fr_decl.A.fun_loc in
      let f, vars, ty_f = conv_def fr.A.fr_decl in
      let vars_as_t =
        List.map (fun (s,_) -> UA.var ~loc s) vars
      in
      let body = conv_term fr.A.fr_body in
      let ax = UA.forall_list ~loc vars
          @@ UA.eq ~loc (UA.app ~loc (UA.var ~loc f) vars_as_t) body in
      let def = UA.rec_ ~loc [f, ty_f, [ax]] in
      [def]
    | A.Stmt_funs_rec {A.fsr_decls; fsr_bodies} ->
      if List.length fsr_decls <> List.length fsr_bodies then (
        Utils.failwithf
          "TIP parser: in `@[%a@`],@ number of declarations and bodies must coincide"
          A.pp_stmt st
      );
      let defs =
        List.map2
          (fun decl body ->
             (* definition becomes a decl + universal axioms *)
             let loc = decl.A.fun_loc in
             let f, vars, ty_f = conv_def decl in
             let vars_as_t =
               List.map (fun (s,_) -> UA.var ~loc s) vars
             in
             let body = conv_term body in
             let ax =
               UA.forall_list ~loc vars @@
               UA.eq ~loc (UA.app ~loc (UA.var ~loc f) vars_as_t) body
             in
             f, ty_f, [ax])
          fsr_decls fsr_bodies
      in
      let def = UA.rec_ ~loc defs in
      [def]

let convert_st_l ?(into=CCVector.create()) l =
  List.iter (fun st -> CCVector.append_list into (convert_st st)) l;
  into

(** {2 Parse + convert} *)

let parse ?mode:_ ?(into=CCVector.create()) src
  : UA.statement CCVector.vector or_error =
  let open CCResult.Infix in
  begin match src with
    | `Stdin -> parse_stdin ()
    | `File f -> parse_file f
  end >|= convert_st_l ~into
