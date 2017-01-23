
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Backend for SMBC} *)

open Nunchaku_core
open Nunchaku_parsers

module TI = TermInner
module T = TermInner.Default
module P = T.P
module U = T.U
module A = Tip_ast
module Res = Problem.Res
module E = CCResult
module S = Scheduling
module Stmt = Statement
module PStmt = Statement.Print(P)(P)

type term = TermInner.Default.t
type ty = term
type problem = (term,ty) Problem.t
type env = (term,ty) Env.t

let name = "smbc"
let section = Utils.Section.make name

let is_available () =
  try
    let res = Sys.command "smbc --help > /dev/null 2> /dev/null" = 0 in
    if res then Utils.debug ~section 3 "smbc is available";
    res
  with Sys_error _ -> false

exception Error of string
exception Out_of_scope of string
exception Conversion_error of T.t
exception Parse_result_error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "[SMBC backend] %s" msg)
      | Out_of_scope msg -> Some (Printf.sprintf "problem is out of scope for SMBC: %s" msg)
      | Conversion_error t ->
        Some (Utils.err_sprintf "problem could not be converted to TIP: %a" P.print t)
      | Parse_result_error msg -> Some ("could not parse result: " ^ msg)
      | _ -> None)

let out_of_scope msg = raise (Out_of_scope msg)
let out_of_scopef msg = Utils.exn_ksprintf msg ~f:out_of_scope


let erase = ID.Erase.create_state ()
let id_to_string =
  let escape_ _id name = match name with
    | "distinct" | "match" | "case" -> name ^ "_"
    | _ -> name
  in
  ID.Erase.to_name erase ~encode:escape_
let id_of_string s = try Some (ID.Erase.of_name erase s) with Not_found -> None

(** {2 Local Transformation}

    We perform a few local transformations.
    In particular, we replace data testers by named functions, and
    give an explicit name to selectors *)

module ID_int_tbl = CCHashtbl.Make(struct
    type t = ID.t * int
    let equal (a,i)(b,j) = ID.equal a b && i=j
    let hash (a,i) = Hashtbl.hash (ID.hash a,i)
  end)

type state = {
  local_statements: A.statement CCVector.vector;
  data_select_tbl: ID.t ID_int_tbl.t;
  data_test_tbl: ID.t ID.Tbl.t;
  env: env;
}

let mk_state (env:env): state = {
  env;
  local_statements=CCVector.create();
  data_select_tbl = ID_int_tbl.create 16;
  data_test_tbl = ID.Tbl.create 16;
}

(* remove and return the new statements *)
let local_statements (st:state): A.statement list =
  let l = CCVector.to_list st.local_statements in
  CCVector.clear st.local_statements;
  l

(** {2 Printing to SMBC} *)

let data_select_fun st c i : ID.t =
  match ID_int_tbl.get st.data_select_tbl (c,i) with
    | Some id -> id
    | None ->
      Utils.failwithf
        "cannot find TIP id for data select `select-%a-%d`" ID.print_full c i

let rec term_to_tip (st:state) (t:term): A.term = match T.repr t with
  | TI.Const id -> A.const (id_to_string id)
  | TI.Var v -> A.const (conv_var v)
  | TI.App (f, l) ->
    let l = List.map (term_to_tip st) l in
    begin match T.repr f with
      | TI.Const id -> A.app (id_to_string id) l
      | TI.Builtin (`DataTest c) ->
        A.app (data_test_fun st c |> id_to_string) l
      | TI.Builtin (`DataSelect (c,i)) ->
        A.app (data_select_fun st c i |> id_to_string) l
      | _ -> List.fold_left A.ho_app (term_to_tip st f) l
    end
  | TI.Builtin b ->
    begin match b with
      | `True -> A.true_
      | `False -> A.false_
      | `Or l -> A.or_ (List.map (term_to_tip st) l)
      | `And l -> A.and_ (List.map (term_to_tip st) l)
      | `Imply (a,b) -> A.imply (term_to_tip st a)(term_to_tip st b)
      | `Ite (a,b,c) -> A.if_ (term_to_tip st a)(term_to_tip st b)(term_to_tip st c)
      | `Eq (a,b) -> A.eq (term_to_tip st a)(term_to_tip st b)
      | `Not a -> A.not_ (term_to_tip st a)
      | `DataTest c -> A.const (data_test_fun st c |> id_to_string)
      | `DataSelect (c,i) -> A.const (data_select_fun st c i |> id_to_string)
      | `Undefined_atom _
      | `Undefined_self _ -> raise (Conversion_error t)
      | `Guard (t,g) ->
        (* use builtin "asserting" *)
        let t = term_to_tip st t in
        let g = U.and_nodup g.Builtin.asserting |> term_to_tip st in
        A.app "asserting" [t; g]
      | `Unparsable _
        -> assert false (* TODO: better error: should not happen *)
    end
  | TI.Bind (Binder.Fun,v,body) ->
    A.fun_ (conv_typed_var v) (term_to_tip  st body)
  | TI.Bind (Binder.Forall,v,body) ->
    A.forall [conv_typed_var v] (term_to_tip st body)
  | TI.Bind (Binder.Exists,v,body) ->
    A.exists [conv_typed_var v] (term_to_tip st body)
  | TI.Bind (Binder.TyForall,_,_)
  | TI.Bind (Binder.Mu,_,_) -> out_of_scopef "cannot convert to TIP µ %a" P.print t
  | TI.Let (v,t,u) ->
    A.let_ [conv_var v, term_to_tip st t] (term_to_tip st u)
  | TI.Match (u,map,def) ->
    let u = term_to_tip st u in
    let cases =
      ID.Map.to_list map
      |> List.map
        (fun (c, (vars,rhs)) ->
           A.Match_case
             (id_to_string c, List.map conv_var vars, term_to_tip st rhs))
    and def = match def with
      | TI.Default_none -> []
      | TI.Default_some (rhs,_) -> [A.Match_default (term_to_tip st rhs)]
    in
    A.match_ u (cases @ def)
  | TI.TyBuiltin _
  | TI.TyArrow _
  | TI.TyMeta _ -> raise (Conversion_error t)

and ty_to_tip(t:term): A.ty = match T.repr t with
  | TI.Const id -> A.ty_const (id_to_string id)
  | TI.Var v -> A.ty_const (conv_var v)
  | TI.App (f, l) ->
    let l = List.map ty_to_tip l in
    begin match T.repr f with
      | TI.Const id -> A.ty_app (id_to_string id) l
      | _ -> out_of_scopef "cannot convert to TIP ty %a" P.print t
    end
  | TI.TyArrow (a,b) -> A.ty_arrow (ty_to_tip a)(ty_to_tip b)
  | TI.TyBuiltin `Prop -> A.ty_bool
  | TI.TyBuiltin `Type -> out_of_scope "cannot encode to TIP TType"
  | _ -> assert false

and conv_typed_var v = conv_var v, ty_to_tip (Var.ty v)
and conv_tyvar v = assert (U.ty_is_Type (Var.ty v)); conv_var v
and conv_var v = id_to_string (Var.id v)

(* a local function for "is-c" data tester *)
and data_test_fun (st:state) (c:ID.t): ID.t =
  let ty_c = Env.find_ty_exn ~env:st.env c in
  let ty_args, c_args, data_ty = U.ty_unfold ty_c in
  assert (ty_args = []); (* mono *)
  try ID.Tbl.find st.data_test_tbl c
  with Not_found ->
    let id = ID.make_f "is-%s" (ID.to_string_slug c) in
    (* define id *)
    let x = "x" in
    let decl = {
      A.fun_ty_vars = [];
      fun_name = id_to_string id;
      fun_args = [x, ty_to_tip data_ty];
      fun_ret = A.ty_bool;
    } in
    (* [match x with c _ -> true | default -> false] *)
    let body =
      let c_vars = List.mapi (fun i _ -> "x_" ^ string_of_int i) c_args in
      A.match_ (A.const x)
        [ A.Match_case (id_to_string c, c_vars, A.true_);
          A.Match_default A.false_;
        ]
    in
    let def = A.fun_def {A.fr_decl=decl; fr_body=body} in
    (* save and declare *)
    Utils.debugf ~section 3 "@[<2>define `is-%a` as@ `@[%a@]`@]"
      (fun k->k ID.print_full c A.pp_stmt def);
    CCVector.push st.local_statements def;
    ID.Tbl.add st.data_test_tbl c id;
    id

let decl_to_tip id ty : A.statement =
  let s = id_to_string id in
  let ty_vars, ty_args, ty_ret = U.ty_unfold ty in
  if U.ty_is_Type ty_ret then (
    assert (ty_vars=[]);
    assert (List.for_all U.ty_is_Type ty_args);
    A.decl_sort s ~arity:(List.length ty_args)
  ) else (
    A.decl_fun s
      ~tyvars:(List.map conv_tyvar ty_vars)
      (List.map ty_to_tip ty_args)
      (ty_to_tip ty_ret)
  )

let decl_attrs_to_tip state (id:ID.t) attrs: A.statement list =
  CCList.filter_map
    (function
      | Stmt.Attr_card_max n ->
        let module CE = Cardinal_encode.Make(T) in
        let ax = CE.encode_max_card (U.ty_const id) n |> term_to_tip state in
        Some (A.assert_ ax)
      | Stmt.Attr_card_min n ->
        let module CE = Cardinal_encode.Make(T) in
        let ax = CE.encode_min_card (U.ty_const id) n |> term_to_tip state in
        Some (A.assert_ ax)
      | _ -> None)
    attrs

let statement_to_tip (state:state) (st:(term,ty)Stmt.t): A.statement list =
  let new_st = match Stmt.view st with
    | Stmt.Decl {Stmt.defined_head=id; defined_ty=ty; defined_attrs=attrs; } ->
      let vars, _, _ = U.ty_unfold ty in
      if vars=[]
      then decl_to_tip id ty :: decl_attrs_to_tip state id attrs
      else out_of_scopef "cannot encode to TIP poly statement %a" PStmt.print st
    | Stmt.Axiom (Stmt.Axiom_std l) ->
      List.map (fun ax -> A.assert_ (term_to_tip state ax)) l
    | Stmt.Axiom (Stmt.Axiom_spec s) ->
      (* TODO: if some variables have type {fun,datatype}, then raise Out_of_scope,
         for SMBC will not be able to handle them *)
      (* first declare, then axiomatize *)
      assert (s.Stmt.spec_ty_vars=[]);
      let decls =
        Stmt.defined_of_spec s
        |> Sequence.map
          (fun {Stmt.defined_head=id; defined_ty=ty; _} ->
             decl_to_tip id ty)
        |> Sequence.to_list
      and axioms =
        s.Stmt.spec_axioms
        |> List.map
          (fun t -> A.assert_ (term_to_tip state t))
      in
      decls @ axioms
    | Stmt.Axiom (Stmt.Axiom_rec l) ->
      let l =
        List.map
          (fun def ->
             if def.Stmt.rec_ty_vars <> [] then (
               out_of_scopef "polymorphic `@[%a@]`" PStmt.print st;
             );
             let {Stmt.defined_head=id; defined_ty=ty; _} = def.Stmt.rec_defined in
             let name = id_to_string id in
             let _, _, ty_ret = U.ty_unfold ty in
             let vars, body = match def.Stmt.rec_eqns with
               | Stmt.Eqn_single (vars, rhs) ->
                 List.map conv_typed_var vars, term_to_tip state rhs
               | Stmt.Eqn_nested _ | Stmt.Eqn_app _ -> assert false
             in
             {A.
               fun_ty_vars=[];
               fun_name=name;
               fun_ret=ty_to_tip ty_ret;
               fun_args=vars;
             }, body)
          l
      in
      begin match l with
        | [decl,body] ->
          [A.fun_rec {A.fr_decl=decl; fr_body=body}]
        | l ->
          let decls, bodies = List.split l in
          [A.funs_rec decls bodies]
      end
    | Stmt.Goal g ->
      let neg_g = term_to_tip state (U.not_ g) in
      [A.assert_not ~ty_vars:[] neg_g]
    | Stmt.TyDef (`Codata,_) -> out_of_scopef "cannot encode Codata %a" PStmt.print st
    | Stmt.TyDef (`Data, l) ->
      (* declare datatypes, along with their selectors *)
      let l =
        List.map
          (fun d ->
             assert (d.Stmt.ty_vars=[]);
             let name = id_to_string d.Stmt.ty_id in
             let cstors =
               ID.Map.values d.Stmt.ty_cstors
               |> Sequence.map
                 (fun c ->
                    let cstor_name = id_to_string c.Stmt.cstor_name in
                    let cstor_args =
                      c.Stmt.cstor_args
                      |> List.mapi
                        (fun i ty ->
                           let id_select =
                             ID.make_f "select-%s-%d" cstor_name i
                           in
                           ID_int_tbl.add state.data_select_tbl
                             (c.Stmt.cstor_name,i) id_select;
                           id_to_string id_select, ty_to_tip ty)
                    in
                    {A.cstor_name; cstor_args})
               |> Sequence.to_list
             in
             name, cstors)
          l
      in
      [A.data [] l]
    | Stmt.Pred (_,_,_)
    | Stmt.Copy _ -> assert false
  in
  local_statements state @ new_st

(* print a problem as TIP *)
let print_pb out (pb:problem): unit =
  let env = Problem.env pb in
  let state = mk_state env in
  Problem.statements pb
  |> CCVector.iter
    (fun st ->
       let l = statement_to_tip state st in
       List.iter (Format.fprintf out "%a@." A.pp_stmt) l);
  Format.fprintf out "(check-sat)@.";
  ()

(** {2 Parsing Model} *)

let error_parse_model msg = raise (Parse_result_error msg)
let error_parse_modelf msg = Utils.exn_ksprintf ~f:error_parse_model msg

module StrMap = CCMap.Make(String)

(* local mapping/typing env for variables *)
type parse_env = [`Var of ty Var.t | `Subst of term] StrMap.t

let empty_env : parse_env = StrMap.empty

let id_of_tip (env:parse_env) (s:string):
  [`Var of _ Var.t | `Const of ID.t | `Undef of ID.t | `Subst of term] =
  (* look first in the local environment for bound variables,
     then in the {!ID.Erase} table *)
  begin match StrMap.get s env with
    | Some (`Var v) -> `Var v
    | Some (`Subst t) -> `Subst t
    | None ->
      begin match id_of_string s with
        | None when s.[0] = '$' ->
          (* domain element. They have the "distinct" property *)
          let id = ID.make_full ~needs_at:false ~distinct:true s in
          ID.Erase.add_name erase s id;
          `Const id
        | None when s.[0] = '?' ->
          (* unknown *)
          let id = ID.make s in
          ID.Erase.add_name erase s id;
          `Undef id
        | Some id -> `Const id
        | None ->
          error_parse_modelf "expected ID, got unknown `%s`" s
      end
  end

let rec term_of_tip (env:parse_env) (t:A.term): term = match t with
  | A.True -> U.true_
  | A.False -> U.false_
  | A.Const c -> term_of_id env c
  | A.App (f,l) ->
    let f = term_of_id env f in
    U.app f (List.map (term_of_tip env) l)
  | A.HO_app (f,a) ->
    U.app (term_of_tip env f) [term_of_tip env a]
  | A.Match (_,_) ->
    (* TODO: how? *)
    error_parse_model "cannot deal with match-based models yet, sorry"
  | A.If (a,b,c) ->
    U.ite (term_of_tip env a)(term_of_tip env b)(term_of_tip env c)
  | A.Let (l,u) ->
    let env = List.fold_left
        (fun env (s,t) ->
           let t = term_of_tip env t in
           StrMap.add s (`Subst t) env)
        env l
    in
    term_of_tip env u
  | A.Fun (v,body) ->
    let env, v = typed_var_of_tip env v in
    let body = term_of_tip env body in
    U.fun_ v body
  | A.Eq (a,b) -> U.eq (term_of_tip env a)(term_of_tip env b)
  | A.Imply (a,b) -> U.imply (term_of_tip env a)(term_of_tip env b)
  | A.And l ->
    let l = List.map (term_of_tip env) l in
    U.and_ l
  | A.Or l ->
    let l = List.map (term_of_tip env) l in
    U.or_ l
  | A.Not a -> U.not_ (term_of_tip env a)
  | A.Forall (v,body) ->
    let env, v = CCList.fold_map typed_var_of_tip env v in
    let body = term_of_tip env body in
    U.forall_l v body
  | A.Exists (v,body) ->
    let env, v = CCList.fold_map typed_var_of_tip env v in
    let body = term_of_tip env body in
    U.exists_l v body
  | A.Cast (_,_) -> assert false

and term_of_id (env:parse_env) (s:string): term = match id_of_tip env s with
  | `Const id -> U.const id
  | `Undef id ->
    (* FIXME: need some other primitive, e.g. "hole", to represent this? *)
    U.undefined_self (U.const id)
  | `Subst t -> t
  | `Var v -> U.var v

and ty_of_tip (ty:A.ty): ty = match ty with
  | A.Ty_bool -> U.ty_prop
  | A.Ty_arrow (l, ret) ->
    U.ty_arrow_l (List.map ty_of_tip l) (ty_of_tip ret)
  | A.Ty_app (f, l) ->
    U.ty_app (term_of_id empty_env f) (List.map ty_of_tip l)

and typed_var_of_tip (env:parse_env) (s,ty) =
  let id = ID.make s in
  let ty = ty_of_tip ty in
  let v = Var.of_id id ~ty in
  StrMap.add s (`Var v) env, v

(* convert a term with functions inside tests into one single function
   with tests in the body.
   Example:
   [if a then (fun x. if x then (fun y.true) else (fun y.false)) else (fun x' y'. x and y)]
   should become
   [fun x y.
    if a then
      if x then true else false
    else x and y]
*)
let extract_to_outer_function (t:term): term =
  let rec merge_ty_lists l1 l2 = match l1, l2 with
    | [], _ | _, [] -> []
    | ty1 :: tail1, ty2 :: tail2 ->
      assert (U.equal ty1 ty2); (* by well-typedness *)
      ty1 :: merge_ty_lists tail1 tail2
  in
  (* first, find the list of variables' types that
     are available in *all* branches in the same order.
     Above it would return [typeof x, typeof y] *)
  let rec extract_ty_args t : ty list = match T.repr t with
    | TI.Bind (Binder.Fun, v, u) -> Var.ty v :: extract_ty_args u
    | TI.Builtin (`Ite (_, a, b)) -> merge_ty_lists (extract_ty_args a) (extract_ty_args b)
    | TI.Match (_, m, def) ->
      assert (not (ID.Map.is_empty m));
      let id, (_, rhs) = ID.Map.min_binding m in
      let args0 = extract_ty_args rhs in
      let m = ID.Map.remove id m in
      let args =
        ID.Map.fold
          (fun _ (_, rhs) m -> merge_ty_lists m (extract_ty_args rhs))
          m args0
      in
      begin match def with
        | TI.Default_none -> args
        | TI.Default_some (rhs,_) ->
          merge_ty_lists args (extract_ty_args rhs)
      end
    | _ -> []
  in
  (* transform [t] to extract its function part outside
     @param vars the list of variables still available to rename
      function parameters in [t]
     @param subst variables already substituted *)
  let rec transform fun_vars subst t = match T.repr t, fun_vars with
    | _, [] ->
      (* no more variables, must be a leaf, just rename variables *)
      U.eval_renaming ~subst t
    | TI.Bind (Binder.Fun, v, body), new_v :: vars_tail ->
      assert (not (Var.Subst.mem ~subst v));
      let subst = Var.Subst.add ~subst v new_v in
      transform vars_tail subst body
    | TI.Builtin (`Ite (a,b,c)), _ ->
      U.ite
        (U.eval_renaming ~subst a)
        (transform fun_vars subst b)
        (transform fun_vars subst c)
    | TI.Match (u, m, def), _ ->
      U.match_with
        (U.eval_renaming ~subst u)
        (ID.Map.map
           (fun (vars, rhs) ->
              let subst, vars =
                CCList.fold_map Var.Subst.rename_var subst vars
              in
              vars, transform fun_vars subst rhs)
           m)
        ~def:(TI.map_default_case (transform fun_vars subst) def)
    | _ ->
      assert false (* [fun_vars=[]] should hold *)
  in
  let ty_args = extract_ty_args t in
  let module TyMo = TypeMono.Make(T) in
  let vars =
    List.mapi
      (fun i ty -> Var.makef ~ty "%s_%d" (TyMo.mangle ~sep:"_" ty) i)
      ty_args
  in
  U.fun_l vars (transform vars Var.Subst.empty t)

(* convert a term into a decision tree *)
let dt_of_term (t:term): (term,ty) Model.DT.t =
  (* split [t] into a list of equations [var = t'] where [var in vars] *)
  let rec get_eqns_exn ~vars t : (_,_) Model.DT.flat_test list =
    let mk_eq = Model.DT.mk_flat_test in
    Utils.debugf 5 "get_eqns @[%a@]" (fun k->k P.print t);
    let fail() =
      error_parse_modelf
        "expected a test <var = term>@ with <var> among [@[%a@]],@ but got `@[%a@]`@]"
        (CCFormat.list Var.print_full) vars P.print t
    in
    match T.repr t with
      | TI.Builtin (`And l) -> CCList.flat_map (get_eqns_exn ~vars) l
      | TI.Builtin (`Eq (t1, t2)) ->
        begin match T.repr t1, T.repr t2 with
          | TI.Var v, _ when List.exists (Var.equal v) vars -> [mk_eq v t2]
          | _, TI.Var v when List.exists (Var.equal v) vars -> [mk_eq v t1]
          | _ -> fail()
        end
      | TI.Var v when List.exists (Var.equal v) vars ->
        assert (U.ty_is_Prop (Var.ty v));
        [mk_eq v U.true_]
      | TI.Var _ ->
        error_parse_modelf
          "expected a boolean variable among @[%a@],@ but got @[%a@]@]"
          (CCFormat.list Var.print_full) vars P.print t
      | _ -> fail()
  in
  let open Sequence.Infix in
  let rec conv_body ~vars t : ((_,_) Model.DT.flat_test list * term) Sequence.t =
    match T.repr t with
      | TI.Builtin (`Ite (a,b,c)) ->
        let tests = get_eqns_exn ~vars a in
        Sequence.append
          (conv_body ~vars b >|= fun (cond,bod) -> tests @ cond, bod)
          (conv_body ~vars c >|= fun (cond,bod) -> cond, bod)
      | TI.Const _ | TI.App _ | TI.Var _ | TI.Bind _ | TI.Builtin _
        ->
        Sequence.return ([], t)
      | TI.Match _ -> Utils.not_implemented "parsing `match` from SMBC" (* TODO *)
      | TI.Let _
      | TI.TyMeta _ | TI.TyArrow _ | TI.TyBuiltin _ -> assert false
  in
  let vars, body = U.fun_unfold t in
  (* change the shape of [body] so it looks more like a decision tree *)
  let cases = conv_body ~vars body |> Sequence.to_list in
  let flat = {
    Model.DT.
    fdt_vars=vars;
    fdt_default=None;
    fdt_cases=cases;
  } in
  let dt = Model.DT.of_flat ~equal:U.equal ~hash:U.hash flat in
  Utils.debugf ~section 5
    "@[<2>turn term `@[%a@]`@ into DT `@[%a@]`@ using ft `@[%a@]`@]"
    (fun k->k P.print body (Model.DT.print P.print' P.print) dt
        (Model.DT.print_flat P.print') flat);
  dt

module A_res = A.Smbc_res

let convert_model ~env (m:A_res.model): (_,_) Model.t =
  let find_kind (t:term): Model.symbol_kind =
    let fail() =
      Utils.warningf Utils.Warn_model_parsing_error
        "cannot find symbol_kind for `@[%a@]`" P.print t;
      Model.Symbol_fun
    in
    match T.repr t with
      | TI.Const id ->
        begin match Env.find_ty ~env id with
          | Some ty ->
            if U.ty_returns_Prop ty then Model.Symbol_prop else Model.Symbol_fun
          | None -> fail()
        end
      | _ -> fail()
  in
  List.fold_left
    (fun m e -> match e with
       | A_res.Ty (ty, dom) ->
         let ty = ty_of_tip ty in
         let dom =
           List.map
             (fun s -> match id_of_tip empty_env s with
                | `Subst _
                | `Var _ -> error_parse_modelf "invalid domain element %s" s
                | `Const id
                | `Undef id -> id)
             dom
         in
         Model.add_finite_type m ty dom
       | A_res.Val (a,b) ->
         let a = term_of_tip empty_env a in
         (* conversion of [b] into a proper decision tree *)
         let b =
           term_of_tip empty_env b
           |> extract_to_outer_function
           |> dt_of_term
         in
         let k = find_kind a in
         Model.add_value m (a,b,k))
    Model.empty m

let convert_res ~env ~info ~meta (res:A_res.t): (_,_) Res.t * S.shortcut = match res with
  | A_res.Timeout -> Res.Unknown [Res.U_timeout info], S.No_shortcut
  | A_res.Unknown s -> Res.Unknown [Res.U_other (info,s)], S.No_shortcut
  | A_res.Unsat when meta.ProblemMetadata.unsat_means_unknown ->
    Res.Unknown [Res.U_incomplete info], S.No_shortcut
  | A_res.Unsat -> Res.Unsat info, S.Shortcut
  | A_res.Sat m ->
    let m = convert_model ~env m in
    Res.Sat (m,info), S.Shortcut

(* parse [stdout, errcode] into a proper result *)
let parse_res ~env ~info ~meta (out:string) (errcode:int): (term,ty) Res.t * S.shortcut =
  if errcode<>0
  then
    let msg = Printf.sprintf "smbc failed with errcode %d, output:\n%s" errcode out in
    Res.Error (Error msg, info), S.Shortcut
  else (
    try
      let lexbuf = Lexing.from_string out in
      Location.set_file lexbuf "<output of smbc>";
      let res = Tip_parser.parse_smbc_res Tip_lexer.token lexbuf in
      convert_res ~env ~info ~meta res
    with e ->
      Res.Error (e,info), S.Shortcut
  )

(** {2 Main Solving} *)

(* step between successive depths in iterative deepening *)
let depth_step_ = 1 (* FUDGE *)

let solve ~deadline pb =
  Utils.debug ~section 1 "calling smbc";
  let now = Unix.gettimeofday() in
  if now +. 0.5 > deadline
  then
    let i = Res.mk_info ~backend:"smbc" ~time:0. () in
    Res.Unknown [Res.U_timeout i], S.No_shortcut
  else (
    let timer = Utils.Time.start_timer () in
    let mk_info ?msg () =
      Res.mk_info ?message:msg
        ~backend:"smbc" ~time:(Utils.Time.get_timer timer) ()
    in
    let timeout = (int_of_float (deadline -. now +. 1.5)) in
    (* call solver and communicate over stdin *)
    let cmd =
      Printf.sprintf "smbc -t %d -nc --depth-step %d --check --stdin 2>&1"
        timeout depth_step_
    in
    Utils.debugf ~section 5 "smbc call: `%s`" (fun k->k cmd);
    (* print problem into a TIP string;
       also serves to check Out_of_scope *)
    try
      let pb_string = CCFormat.sprintf "@[<v>%a@]@." print_pb pb in
      let fut =
        S.popen cmd
          ~f:(fun (stdin,stdout) ->
            Utils.debugf ~lock:true ~section 5 "smbc input:@ %s" (fun k->k pb_string);
            (* send problem *)
            output_string stdin pb_string;
            flush stdin;
            close_out stdin;
            CCIO.read_all stdout)
      in
      begin match S.Fut.get fut with
        | S.Fut.Done (E.Ok (stdout, errcode)) ->
          Utils.debugf ~lock:true ~section 2
            "@[<2>smbc exited with %d, stdout:@ `%s`@]"
            (fun k->k errcode stdout);
          let info = mk_info() in
          (* need environment to re-infer some types *)
          let env = Problem.env pb in
          parse_res ~env ~info ~meta:(Problem.metadata pb) stdout errcode
        | S.Fut.Done (E.Error e) ->
          let info = mk_info() in
          Res.Error (e,info), S.Shortcut
        | S.Fut.Stopped ->
          let info = mk_info() in
          Res.Unknown [Res.U_timeout info], S.No_shortcut
        | S.Fut.Fail e ->
          (* return error *)
          Utils.debugf ~lock:true ~section 1 "@[<2>smbc failed with@ `%s`@]"
            (fun k->k (Printexc.to_string e));
          let info = mk_info() in
          Res.Error (e,info), S.Shortcut
      end
    with Out_of_scope msg ->
      Utils.debugf ~section 3 "@[out of scope because:@ %s@]"
        (fun k->k msg);
      let info = mk_info ~msg () in
      Res.Unknown [Res.U_out_of_scope info], S.No_shortcut (* out of scope *)
  )

let call_real ~print_model ~prio problem =
  S.Task.make ?prio
    (fun ~deadline () ->
       let res, short = solve ~deadline problem in
       Utils.debugf ~section 2 "@[<2>smbc result:@ %a@]"
         (fun k->k Res.print_head res);
       begin match res with
         | Res.Sat (m,_) when print_model ->
           let pp_ty oc _ = CCFormat.string oc "$i" in
           Format.printf "@[<2>raw smbc model:@ @[%a@]@]@."
             (Model.print P.print' pp_ty) m
         | _ -> ()
       end;
       res, short)

(* solve problem before [deadline] *)
let call ?(print_model=false) ?prio ~print ~dump problem =
  if print then (
    let module P_pb = Problem.Print(P)(P) in
    Format.printf "@[<v2>SMBC problem:@ %a@]@." P_pb.print problem;
  );
  begin match dump with
    | None -> call_real ~print_model ~prio problem
    | Some file ->
      let file = file ^ ".smbc.smt2" in
      Utils.debugf ~section 1 "output smbc problem into `%s`" (fun k->k file);
      CCIO.with_out file
        (fun oc ->
           let out = Format.formatter_of_out_channel oc in
           Format.fprintf out "@[<v>; generated by nunchaku@ %a@]@." print_pb problem);
      let i = Res.mk_info ~backend:"smbc" ~time:0. () in
      S.Task.return (Res.Unknown [Res.U_other (i, "--dump")]) S.No_shortcut
  end

let pipe ?(print_model=false) ~print ~dump () =
  let input_spec =
    Transform.Features.(of_list [
        Ty, Mono; If_then_else, Present;
        Eqn, Eqn_single; Codata, Absent;
        Copy, Absent; Ind_preds, Absent; Prop_args, Present;
      ])
  in
  let encode pb =
    let prio = 25 in
    call ~print_model ~prio ~print ~dump pb, ()
  in
  Transform.make
    ~input_spec
    ~name ~encode ~decode:(fun _ x -> x) ()
