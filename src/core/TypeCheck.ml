
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Type Checking of a problem} *)

module TI = TermInner

let section = Utils.Section.(make ~parent:root "ty_check")

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some (Utils.err_sprintf "broken invariant: %s" msg)
      | _ -> None)

let error_ msg = raise (Error msg)
let errorf_ msg = CCFormat.ksprintf ~f:error_ msg

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)

  type 'inv env = (T.t, T.t, 'inv) Env.t

  let empty_env () = Env.create ()

  let prop = U.ty_prop
  let prop1 = U.ty_arrow prop prop
  let prop2 = U.ty_arrow prop (U.ty_arrow prop prop)

  let find_ty_ ~env id =
    try Env.find_ty_exn ~env id
    with Not_found ->
      errorf_ "identifier %a not defined in scope" ID.print_full id

  let err_ty_mismatch t exp act =
    errorf_ "@[<2>type of `@[%a@]` should be `@[%a@]`,@ but is `@[%a@]`@]"
      P.print t P.print exp P.print act

  (* check that [ty = prop] *)
  let check_prop t ty =
    if not (U.ty_is_Prop ty)
    then err_ty_mismatch t prop ty

  (* check that [ty_a = ty_b] *)
  let check_same_ a b ty_a ty_b =
    if not (U.equal ty_a ty_b)
    then errorf_
        "@[<2>expected `@[%a@]` : `@[%a@]@ and@ \
        `@[%a@]` : `@[%a@]` to have the same type@]"
        P.print a P.print ty_a P.print b P.print ty_b;
    ()

  module VarSet = Var.Set(T)

  (* check invariants recursively, return type of term *)
  let rec check ~env bound t =
    match T.repr t with
    | TI.Const id -> find_ty_ ~env id
    | TI.Builtin b ->
        begin match b with
          | `Imply -> prop2
          | `Or
          | `And -> assert false (* should be handled below *)
          | `Not -> prop1
          | `True
          | `False -> prop
          | `Ite (a,b,c) ->
              let tya = check ~env bound a in
              let tyb = check ~env bound b in
              let tyc = check ~env bound c in
              check_prop a tya;
              check_same_ b c tyb tyc;
              tyb
          | `Equiv (a,b) ->
              let tya = check ~env bound a in
              let tyb = check ~env bound b in
              check_prop a tya;
              check_prop b tyb;
              prop
          | `Eq (a,b) ->
              let tya = check ~env bound a in
              let tyb = check ~env bound b in
              check_same_ a b tya tyb;
              prop
          | `DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = find_ty_ ~env id in
              U.ty_arrow (U.ty_returns ty) prop
          | `DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = find_ty_ ~env id in
              begin match U.get_ty_arg ty n with
              | Some ty_arg ->
                  U.ty_arrow (U.ty_returns ty) ty_arg
              | _ ->
                  error_ "cannot infer type, wrong argument to DataSelect"
              end
          | `Undefined (_,t) -> check ~env bound t
          | `Guard (t, g) ->
              List.iter (check_is_prop ~env bound) g.TI.Builtin.asserting;
              List.iter (check_is_prop ~env bound) g.TI.Builtin.assuming;
              check ~env bound t
        end
    | TI.Var v ->
        if not (VarSet.mem v bound)
        then errorf_ "variable %a not bound in scope" Var.print_full v;
        Var.ty v
    | TI.App (f,l) ->
        begin match T.repr f with
          | TI.Builtin (`And | `Or) ->
              List.iter (check_is_prop ~env bound) l;
              prop
          | _ -> U.ty_apply (check ~env bound f) (List.map (check ~env bound) l)
        end
    | TI.Bind (b,v,t) ->
        let bound' = VarSet.add v bound in
        begin match b with
        | `Forall
        | `Exists
        | `Mu ->
            check_var ~env bound v;
            check ~env bound' t
        | `Fun ->
            check_var ~env bound v;
            if U.ty_returns_Type (Var.ty v)
            then U.ty_forall v (check ~env bound' t)
            else U.ty_arrow (Var.ty v) (check ~env bound' t)
        | `TyForall ->
            check_ty_var ~env bound t v;
            U.ty_type
        end
    | TI.Let (v,t',u) ->
        let ty_t' = check ~env bound t in
        check_var ~env bound v;
        check_same_ (U.var v) t' (Var.ty v) ty_t';
        let bound' = VarSet.add v bound in
        check ~env bound' u
    | TI.Match (_,m) ->
        (* TODO : check variables and each branch *)
        let _, (_, rhs) = ID.Map.choose m in
        check ~env bound rhs
    | TI.TyMeta _ -> assert false
    | TI.TyBuiltin b ->
        begin match b with
        | `Kind -> failwith "Term_ho.ty: kind has no type"
        | `Type -> U.ty_kind
        | `Prop -> U.ty_type
        end
    | TI.TyArrow (a,b) ->
        check_is_ty ~env bound a;
        check_is_ty ~env bound b;
        U.ty_type

  and check_is_prop ~env bound t =
    let ty = check ~env bound t in
    check_prop t ty;
    ()

  and check_var ~env bound v =
    let _ = check ~env bound (Var.ty v) in
    ()

  and check_ty_var ~env bound t v =
    let tyv = check ~env bound (Var.ty v) in
    if not (U.ty_is_Type tyv) then err_ty_mismatch t U.ty_type tyv;
    ()

  and check_is_ty ~env bound t =
    let ty = check ~env bound t in
    if not (U.ty_is_Type ty) then err_ty_mismatch t U.ty_type ty;
    ()

  let check_statement env st =
    Utils.debugf ~section 2 "@[<2>type check@ `@[%a@]`@]"
      (fun k-> let module PStmt = Statement.Print(P)(P) in k PStmt.print st);
    let check_top env bound () t = ignore (check ~env bound t) in
    Statement.fold_bind VarSet.empty () st
      ~bind:(fun set v ->
        check_var ~env set v; VarSet.add v set)
      ~term:(check_top env) ~ty:(check_top env);
    (* update env *)
    Env.add_statement ~env st

  let check_problem ?(env=empty_env ()) pb =
    let _ = CCVector.fold check_statement env (Problem.statements pb) in
    ()
end
