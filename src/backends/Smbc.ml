
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
module St = Statement
module PSt = Statement.Print(P)(P)

type term = TermInner.Default.t
type ty = term
type problem = (term,ty) Problem.t

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
exception Conversion_error
exception Parse_result_error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "[SMBC backend] %s" msg)
      | Out_of_scope msg -> Some (Printf.sprintf "problem is out of scope for SMBC: %s" msg)
      | Conversion_error -> Some "problem could not be converted to TIP"
      | Parse_result_error msg -> Some ("could not parse result: " ^ msg)
      | _ -> None)

let error_ msg = raise (Error msg)
let errorf msg = Utils.exn_ksprintf msg ~f:error_

let out_of_scope msg = raise (Out_of_scope msg)
let out_of_scopef msg = Utils.exn_ksprintf msg ~f:out_of_scope


let erase = ID.Erase.create_state ()
let id_to_string id = ID.Erase.to_name erase id
let id_of_string s = try Some (ID.Erase.of_name erase s) with Not_found -> None

(** {2 Printing to SMBC} *)

let rec term_to_tip(t:term): A.term = match T.repr t with
  | TI.Const id -> A.const (id_to_string id)
  | TI.Var v -> A.const (conv_var v)
  | TI.App (f, l) ->
    let l = List.map term_to_tip l in
    begin match T.repr f with
      | TI.Const id -> A.app (id_to_string id) l
      | _ -> List.fold_left A.ho_app (term_to_tip f) l
    end
  | TI.Builtin b ->
    begin match b with
      | `True -> A.true_
      | `False -> A.false_
      | `Or l
      | `And l -> A.and_ (List.map term_to_tip l)
      | `Imply (a,b) -> A.imply (term_to_tip a)(term_to_tip b)
      | `Ite (a,b,c) -> A.if_ (term_to_tip a)(term_to_tip b)(term_to_tip c)
      | `Eq (a,b) -> A.eq (term_to_tip a)(term_to_tip b)
      | `Not a -> A.not_ (term_to_tip a)
      | `DataTest _ -> out_of_scopef "cannot convert to TIP data test %a" P.print t
      | `DataSelect _ -> out_of_scopef "cannot convert to TIP data select %a" P.print t
      | `Undefined_atom _
      | `Undefined_self (_,_) -> raise Conversion_error
      | `Unparsable _
      | `Guard _ -> assert false (* TODO: better error: should not happen *)
    end
  | TI.Bind (`Fun,v,body) ->
    A.fun_ (conv_typed_var v) (term_to_tip body)
  | TI.Bind (`Forall,v,body) ->
    A.forall [conv_typed_var v] (term_to_tip body)
  | TI.Bind (`Exists,v,body) ->
    A.exists [conv_typed_var v] (term_to_tip body)
  | TI.Bind (`TyForall,_,_)
  | TI.Bind (`Mu,_,_) -> out_of_scopef "cannot convert to TIP µ %a" P.print t
  | TI.Let (v,t,u) ->
    A.let_ [conv_var v, term_to_tip t] (term_to_tip u)
  | TI.Match (u,map) ->
    let u = term_to_tip u in
    let cases =
       ID.Map.to_list map
       |> List.map
         (fun (c, (vars,rhs)) ->
            A.Match_case (id_to_string c, List.map conv_var vars, term_to_tip rhs))
    in
    A.match_ u cases
  | TI.TyBuiltin _
  | TI.TyArrow _
  | TI.TyMeta _ -> raise Conversion_error

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

let statement_to_tip (st:(term,ty)St.t): A.statement list = match St.view st with
  | St.Decl (id,ty,_) ->
    let vars, _, _ = U.ty_unfold ty in
    if vars=[]
    then [decl_to_tip id ty]
    else out_of_scopef "cannot encode to TIP poly statement %a" PSt.print st
  | St.Axiom (St.Axiom_std l) ->
    List.map (fun ax -> A.assert_ (term_to_tip ax)) l
  | St.Axiom (St.Axiom_spec s) ->
    (* TODO: if some variables have type {fun,datatype}, then raise Out_of_scope,
       for SMBC will not be able to handle them *)
    (* first declare, then axiomatize *)
    assert (s.St.spec_ty_vars=[]);
    let decls =
      St.defined_of_spec s
      |> Sequence.map
        (fun {St.defined_head=id; defined_ty=ty} ->
           decl_to_tip id ty)
      |> Sequence.to_list
    and axioms =
      s.St.spec_axioms
      |> List.map
        (fun t -> A.assert_ (term_to_tip t))
    in
    decls @ axioms
  | St.Axiom (St.Axiom_rec l) ->
    let l =
      List.map
        (fun def ->
           if def.St.rec_ty_vars <> [] then out_of_scopef "polymorphic `@[%a@]`" PSt.print st;
           let {St.defined_head=id; defined_ty=ty} = def.St.rec_defined in
           let name = id_to_string id in
           let _, _, ty_ret = U.ty_unfold ty in
           let vars, body = match def.St.rec_eqns with
             | St.Eqn_single (vars, rhs) ->
               List.map conv_typed_var vars, term_to_tip rhs
             | St.Eqn_nested _ | St.Eqn_app _ -> assert false
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
  | St.Goal g ->
    let neg_g = term_to_tip (U.not_ g) in
    [A.assert_not ~ty_vars:[] neg_g]
  | St.TyDef (`Codata,_) -> out_of_scopef "cannot encode Codata %a" PSt.print st
  | St.TyDef (`Data, l) ->
    let l =
      List.map
        (fun d ->
           assert (d.St.ty_vars=[]);
           let name = id_to_string d.St.ty_id in
           let cstors =
             ID.Map.values d.St.ty_cstors
             |> Sequence.map
               (fun  c ->
                  let cstor_name = id_to_string c.St.cstor_name in
                  let cstor_args =
                    c.St.cstor_args
                    |> List.mapi
                      (fun i ty -> Printf.sprintf "%s_%d" cstor_name i, ty_to_tip ty)
                  in
                  {A.cstor_name; cstor_args})
             |> Sequence.to_list
           in
           name, cstors)
        l
    in
    [A.data [] l]
  | St.Pred (_,_,_)
  | St.Copy _ -> assert false

(* print a problem as TIP *)
let print_pb out (pb:problem): unit =
  Problem.statements pb
  |> CCVector.iter
    (fun st ->
       let l = statement_to_tip st in
       List.iter (Format.fprintf out "%a@." A.pp_stmt) l);
  ()

(** {2 Parsing Model} *)

let error_parse_model msg = raise (Parse_result_error msg)
let error_parse_modelf msg = Utils.exn_ksprintf ~f:error_parse_model msg

module StrMap = CCMap.Make(String)

(* local mapping/typing env for variables *)
type env = [`Var of ty Var.t | `Subst of term] StrMap.t

let empty_env : env = StrMap.empty

let id_of_tip (env:env) (s:string):
  [`Var of _ Var.t | `Const of ID.t | `Undef of ID.t | `Subst of term] =
  begin match id_of_string s with
    | None when s.[0] = '$' ->
      (* domain element *)
      let id = ID.make s in
      ID.Erase.add_name erase s id;
      `Const id
    | None when s.[0] = '?' ->
      (* unknown *)
      let id = ID.make s in
      ID.Erase.add_name erase s id;
      `Undef id
    | Some id -> `Const id
    | None ->
      begin match StrMap.get s env with
        | Some (`Var v) -> `Var v
        | Some (`Subst t) -> `Subst t
        | None ->
          error_parse_modelf "expected ID, got unknown `%s`" s
      end
  end

let rec term_of_tip (env:env) (t:A.term): term = match t with
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

and term_of_id (env:env) (s:string): term = match id_of_tip env s with
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

and typed_var_of_tip (env:env) (s,ty) =
  let id = ID.make s in
  let ty = ty_of_tip ty in
  let v = Var.of_id id ~ty in
  StrMap.add s (`Var v) env, v

(* convert a term into a decision tree *)
let dt_of_term (t:term): (term,ty) Model.DT.t =
  (* split [t] into a list of equations [var = t'] where [var in vars] *)
  let rec get_eqns_exn ~vars t : (_,_) Model.DT.flat_test list =
    let mk_eq = Model.DT.mk_flat_test in
    Utils.debugf 5 "get_eqns @[%a@]" (fun k->k P.print t);
    let fail() =
      error_parse_modelf
        "expected a test <var = term>@ with <var> among @[%a@],@ but got `@[%a@]`@]"
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
  let cases = conv_body ~vars t |> Sequence.to_list in
  let flat = {
    Model.DT.
    fdt_vars=vars;
    fdt_default=None;
    fdt_cases=cases;
  } in
  let dt = Model.DT.of_flat ~equal:U.equal ~hash:U.hash flat in
  Utils.debugf ~section 5 "@[<2>turn term `@[%a@]`@ into DT `@[%a@]`@]"
    (fun k->k P.print body (Model.DT.print P.print') dt);
  dt

module A_res = A.Smbc_res

let convert_model (m:A_res.model): (_,_) Model.t =
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
         let b = term_of_tip empty_env b |> dt_of_term in
         (* TODO: find actual kind *)
         let k = Model.Symbol_fun in
         Model.add_value m (a,b,k))
    Model.empty m

let convert_res (res:A_res.t): (_,_) Res.t * S.shortcut = match res with
  | A_res.Timeout -> Res.Timeout, S.No_shortcut
  | A_res.Unknown _ -> Res.Unknown, S.No_shortcut
  | A_res.Unsat -> Res.Unsat, S.Shortcut
  | A_res.Sat m ->
    let m = convert_model m in
    Res.Sat m, S.Shortcut

(* parse [stdout, errcode] into a proper result *)
let parse_res (out:string) (errcode:int): (term,ty) Res.t * S.shortcut =
  if errcode<>0
  then
    let msg = Printf.sprintf "smbc failed with errcode %d, output:\n%s" errcode out in
    Res.Error (Error msg), S.Shortcut
  else (
    try
      let lexbuf = Lexing.from_string out in
      Location.set_file lexbuf "<output of smbc>";
      let res = Tip_parser.parse_smbc_res Tip_lexer.token lexbuf in
      convert_res res
    with e ->
      Res.Error e, S.Shortcut
  )

(** {2 Main Solving} *)

let solve ~deadline pb =
  Utils.debug ~section 1 "calling smbc";
  let now = Unix.gettimeofday() in
  if now +. 0.5 > deadline
  then Res.Timeout, S.No_shortcut
  else (
    let timeout = (int_of_float (deadline -. now +. 1.5)) in
    (* call solver and communicate over stdin *)
    let cmd = Printf.sprintf "smbc -t %d -nc --stdin 2>&1" timeout in
    Utils.debugf ~section 5 "smbc call: `%s`" (fun k->k cmd);
    let fut =
      S.popen cmd
        ~f:(fun (stdin,stdout) ->
          Utils.debugf ~lock:true ~section 5 "smbc input:@ @[<v>%a@]" (fun k->k print_pb pb);
          (* send problem *)
          let fmt = Format.formatter_of_out_channel stdin in
          Format.fprintf fmt "%a@." print_pb pb;
          flush stdin;
          close_out stdin;
          CCIO.read_all stdout)
    in
    match S.Fut.get fut with
      | S.Fut.Done (E.Ok (stdout, errcode)) ->
        Utils.debugf ~lock:true ~section 2
          "@[<2>smbc exited with %d, stdout:@ `%s`@]"
          (fun k->k errcode stdout);
        parse_res stdout errcode
      | S.Fut.Fail (Out_of_scope msg)
      | S.Fut.Done (E.Error (Out_of_scope msg)) ->
        Utils.debugf ~section 3 "@[out of scope because:@ %s@]"
          (fun k->k msg);
        Res.Out_of_scope, S.No_shortcut (* out of scope *)
      | S.Fut.Done (E.Error e) ->
        Res.Error e, S.Shortcut
      | S.Fut.Stopped ->
        Res.Timeout, S.No_shortcut
      | S.Fut.Fail e ->
        (* return error *)
        Utils.debugf ~lock:true ~section 1 "@[<2>smbc failed with@ `%s`@]"
          (fun k->k (Printexc.to_string e));
        Res.Error e, S.Shortcut
  )

(* solve problem before [deadline] *)
let call ?(print_model=false) ?prio ~print problem =
  if print then (
    let module P_pb = Problem.Print(P)(P) in
    Format.printf "@[<v2>SMBC problem:@ %a@]@." P_pb.print problem;
  );
  S.Task.make ?prio
    (fun ~deadline () ->
       let res, short = solve ~deadline problem in
       Utils.debugf ~section 2 "@[<2>smbc result:@ %a@]"
         (fun k->k Res.print_head res);
       begin match res with
         | Res.Sat m when print_model ->
           let pp_ty oc _ = CCFormat.string oc "$i" in
           Format.printf "@[<2>raw smbc model:@ @[%a@]@]@."
             (Model.print P.print' pp_ty) m
         | _ -> ()
       end;
       res, short)

let pipe ?(print_model=false) ~print () =
  let input_spec =
    Transform.Features.(of_list [
        Ty, Mono; If_then_else, Present;
        Eqn, Eqn_single; Codata, Absent;
        Copy, Absent; Ind_preds, Absent; Prop_args, Present;
        ])
  in
  let encode pb =
    let prio = 25 in
    call ~print_model ~prio ~print pb, ()
  in
  Transform.make
    ~input_spec
    ~name ~encode ~decode:(fun _ x -> x) ()
