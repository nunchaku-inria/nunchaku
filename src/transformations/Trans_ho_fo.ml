
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Conversion HO/FO} *)

open Nunchaku_core

module TI = TermInner

module Of_ho(T : TI.S) = struct
  module Subst = Var.Subst
  module P = TI.Print(T)
  module U = TI.Util(T)

  exception NotInFO of string

  let section = Utils.Section.make "to_fo"

  let () = Printexc.register_printer
      (function
        | NotInFO msg -> Some(Utils.err_sprintf "term_mono:@ %s" msg)
        | _ -> None)

  let fail_ msg = raise (NotInFO msg)
  let failf msg = Utils.exn_ksprintf ~f:fail_ msg

  let fail_ t msg =
    failf
      "@[<2>term `@[%a@]` is not in the first-order fragment:@ %s@]"
      P.pp t msg

  let rec conv_ty t = match T.repr t with
    | TI.Var _ -> fail_ t "variable in type"
    | TI.TyBuiltin b ->
      begin match b with
        | `Prop -> FO.Ty.builtin `Prop
        | `Unitype -> FO.Ty.builtin `Unitype
        | `Kind -> fail_ t "kind belongs to HO fragment"
        | `Type -> fail_ t "type belongs to HO fragment"
      end
    | TI.Const id -> FO.Ty.const id
    | TI.App (f,l) ->
      begin match T.repr f with
        | TI.Const id -> FO.Ty.app id (List.map conv_ty l)
        | _ -> fail_ t "non-constant application"
      end
    | TI.TyArrow _ -> fail_ t "arrow in atomic type"
    | TI.Let _
    | TI.Match _
    | TI.Builtin _
    | TI.Bind _ -> fail_ t "not a type"
    | TI.TyMeta _ -> assert false

  let conv_var v = Var.update_ty ~f:conv_ty v

  (* find arguments *)
  let rec flat_arrow_ t = match T.repr t with
    | TI.TyArrow (a, b) ->
      let args, ret = flat_arrow_ b in
      a :: args, ret
    | _ -> [], t

  let conv_top_ty t =
    let args, ret = flat_arrow_ t in
    let args = List.map (conv_ty ) args
    and ret = conv_ty ret in
    args, ret

  let rec conv_term ~env t = match T.repr t with
    | TI.Const id -> FO.T.const id
    | TI.Var v -> FO.T.var (conv_var v)
    | TI.Let (v,t,u) ->
      FO.T.let_ (conv_var v) (conv_term ~env t) (conv_term ~env u)
    | TI.Builtin (`Ite (a,b,c)) ->
      FO.T.ite
        (conv_term ~env a) (conv_term ~env b) (conv_term ~env c)
    | TI.Builtin (`Undefined_self t) ->
      FO.T.undefined (conv_term ~env t)
    | TI.Builtin (`Undefined_atom (c,ty)) ->
      FO.T.undefined_atom c (conv_top_ty ty) []
    | TI.Builtin (`Unparsable ty) -> FO.T.unparsable (conv_ty ty)
    | TI.Builtin `True -> FO.T.true_
    | TI.Builtin `False -> FO.T.false_
    | TI.Builtin (`Eq (a,b)) ->
      (* forbid equality between functions *)
      let ty = U.ty_exn ~env a in
      begin match T.repr ty with
        | TI.TyArrow _
        | TI.Bind (Binder.TyForall, _, _) -> fail_ t "equality between functions";
        | TI.TyBuiltin `Prop ->
          FO.T.equiv (conv_term ~env a) (conv_term ~env b)
        | _ ->
          FO.T.eq (conv_term ~env a) (conv_term ~env b)
      end
    | TI.Builtin (`Not t) -> FO.T.not_ (conv_term ~env t)
    | TI.Builtin (`And l) -> FO.T.and_ (List.map (conv_term ~env) l)
    | TI.Builtin (`Or l) -> FO.T.or_ (List.map (conv_term ~env) l)
    | TI.Builtin (`Imply (a,b)) ->
      FO.T.imply (conv_term ~env a) (conv_term ~env b)
    | TI.App (f, l) ->
      begin match T.repr f, l with
        | TI.Const id, _ -> FO.T.app id (List.map (conv_term ~env) l)
        | TI.Builtin (`Undefined_atom (c,ty)), _ ->
          let l = List.map (conv_term ~env) l in
          FO.T.undefined_atom c (conv_top_ty ty) l
        | TI.Builtin (`DataTest c), [t] ->
          FO.T.data_test c (conv_term ~env t)
        | TI.Builtin (`DataSelect (c,n)), [t] ->
          FO.T.data_select c n (conv_term ~env t)
        | _ -> fail_ t "application of non-constant term"
      end
    | TI.Bind (Binder.Fun,v,t) ->
      FO.T.fun_ (conv_var v) (conv_term ~env t)
    | TI.Bind (Binder.Mu,v,t) ->
      FO.T.mu (conv_var v) (conv_term ~env t)
    | TI.Bind (Binder.Forall, v,f) ->
      FO.T.forall (conv_var v) (conv_term ~env f)
    | TI.Bind (Binder.Exists, v,f) ->
      FO.T.exists (conv_var v) (conv_term ~env f)
    | TI.Builtin (`Card_at_least (ty,n)) ->
      FO.T.card_at_least (conv_ty ty) n
    | TI.Match _ -> fail_ t "no case in FO terms"
    | TI.Builtin (`Guard _) -> fail_ t "no guards (assert/assume) in FO"
    | TI.Builtin (`DataSelect _ | `DataTest _) ->
      fail_ t "no unapplied data-select/test in FO"
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> fail_ t "no types in FO terms"
    | TI.Bind (Binder.TyForall,_,_) -> fail_ t "no polymorphic types in FO types"
    | TI.TyMeta _ -> assert false

  let conv_form ~env f =
    Utils.debugf 3 ~section
      "@[<2>convert to FO the formula@ `@[%a@]`@]" (fun k -> k P.pp f);
    conv_term ~env f

  let convert_eqns
    : head:ID.t -> env:(T.t,T.t) Env.t -> (T.t,T.t) Statement.equations -> FO.T.t list
    = fun ~head ~env eqns ->
      let module St = Statement in
      let conv_eqn (vars, args, rhs, side) =
        let vars = List.map conv_var vars in
        let lhs = FO.T.app head args in
        let f =
          if U.ty_returns_Prop (Env.find_ty_exn ~env head)
          then FO.T.equiv lhs (conv_term ~env rhs)
          else FO.T.eq lhs (conv_term ~env rhs)
        in
        (* add side conditions *)
        let side = List.map (conv_form ~env) side in
        let f = if side=[] then f else FO.T.imply (FO.T.and_ side) f in
        List.fold_right FO.T.forall vars f
      in
      match eqns with
        | St.Eqn_single (vars,rhs) ->
          (* [id = fun vars. rhs] *)
          let vars = List.map conv_var vars in
          [ FO.T.eq
              (FO.T.const head)
              (List.fold_right FO.T.fun_ vars (conv_term ~env rhs)) ]
        | St.Eqn_app (_,vars,lhs,rhs) ->
          (* [id = fun vars. rhs] *)
          let vars = List.map conv_var vars in
          let lhs = conv_term ~env lhs in
          let rhs = conv_term ~env rhs in
          [ List.fold_right FO.T.forall vars (FO.T.eq lhs rhs) ]
        | St.Eqn_nested l ->
          List.map
            (fun (vars,args,rhs,side) ->
               conv_eqn (vars, List.map (conv_term ~env) args, rhs, side))
            l

  let conv_attrs =
    CCList.filter_map
      (function
        | Statement.Attr_pseudo_prop -> Some FO.Attr_pseudo_prop
        | Statement.Attr_pseudo_true -> Some FO.Attr_pseudo_true
        | Statement.Attr_card_max_hint n -> Some (FO.Attr_card_hint (`Max, n))
        | Statement.Attr_card_min_hint n -> Some (FO.Attr_card_hint (`Min, n))
        | Statement.Attr_can_be_empty -> Some FO.Attr_can_be_empty
        | _ -> None)

  let convert_statement ~env st =
    let module St = Statement in
    match St.view st with
      | St.Decl {St.defined_ty=ty; defined_attrs=attrs;defined_head=id} ->
        let _, _, ret = U.ty_unfold ty in
        let attrs' = conv_attrs attrs in
        let st' =
          if U.ty_is_Type ret
          then
            let n = U.ty_num_param ty in
            FO.TyDecl (id, n, attrs')
          else
            let ty = conv_top_ty ty in
            FO.Decl (id, ty, attrs')
        in
        (* additional statements, obtained from attributes *)
        let others =
          CCList.filter_map
            (function
              | St.Attr_card_max n -> Some (FO.CardBound (id, `Max, n))
              | St.Attr_card_min n -> Some (FO.CardBound (id, `Min, n))
              | St.Attr_infinite ->
                failf "@[<2>infinite type `%a`@ should have been eliminated@]" ID.pp id
              | _ -> None)
            attrs
        in
        st' :: others
      | St.Axiom a ->
        let mk_ax x = FO.Axiom x in
        begin match a with
          | St.Axiom_std l ->
            List.map (fun ax -> conv_form  ~env ax |> mk_ax) l
          | St.Axiom_spec s ->
            (* first declare all types; then push axioms *)
            let decls = List.rev_map
                (fun def ->
                   let ty = conv_top_ty def.St.defined_ty in
                   let head = def.St.defined_head in
                   FO.Decl (head, ty, []))
                s.St.spec_defined
            and ax = List.map
                (fun ax -> ax |> conv_form ~env |> mk_ax)
                s.St.spec_axioms
            in
            List.rev_append decls ax
          | St.Axiom_rec s ->
            (* first declare all types; then push axioms *)
            let decls =
              List.rev_map
                (fun def ->
                   (* first, declare symbol *)
                   let d = def.St.rec_defined in
                   let ty = conv_top_ty d.St.defined_ty in
                   let head = d.St.defined_head in
                   FO.Decl (head, ty, []))
                s
            and axioms =
              CCList.flat_map
                (fun def ->
                   (* transform equations *)
                   let head = def.St.rec_defined.St.defined_head in
                   let l = convert_eqns ~head ~env def.St.rec_eqns in
                   List.map mk_ax l)
                s
            in
            List.rev_append decls axioms
        end
      | St.Goal f ->
        [ FO.Goal (conv_form ~env f) ]
      | St.Copy _ -> assert false
      | St.Pred _ -> assert false
      | St.TyDef (k, l) ->
        let convert_cstor c =
          {FO.
            cstor_name=c.St.cstor_name;
            cstor_args=List.map conv_ty c.St.cstor_args;
          }
        in
        (* gather all variables *)
        let tys_vars =
          CCList.flat_map (fun tydef -> List.map Var.id tydef.St.ty_vars) l
        (* convert declarations *)
        and tys_defs = List.map
            (fun tydef ->
               let id = tydef.St.ty_id in
               let cstors = ID.Map.map convert_cstor tydef.St.ty_cstors in
               {FO.ty_name=id; ty_cstors=cstors; }
            ) l
        in
        let l = {FO.tys_vars; tys_defs; } in
        [ FO.MutualTypes (k, l) ]

  let convert_problem p =
    let meta = Problem.metadata p in
    let env = Problem.env p in
    let res =
      CCVector.flat_map_list
        (convert_statement ~env)
        (Problem.statements p)
    in
    FO.Problem.make ~meta res
end

module To_ho(T : TI.S) = struct
  module U = TI.Util(T)

  let rec convert_ty t = match FO.Ty.view t with
    | FO.TyBuiltin b ->
      let b = match b with
        | `Prop -> `Prop
        | `Unitype -> `Unitype
      in U.ty_builtin b
    | FO.TyApp (f,l) ->
      let l = List.map convert_ty l in
      U.ty_app (U.ty_const f) l

  let convert_top_ty (l,ret): T.t =
    let args = List.map convert_ty l in
    let ret = convert_ty ret in
    U.ty_arrow_l args ret

  let rec convert_term t =
    match FO.T.view t with
      | FO.Builtin b ->
        let b = match b with
          | `Int _ -> Utils.not_implemented "conversion from int"
        in
        U.builtin b
      | FO.True -> U.true_
      | FO.False -> U.false_
      | FO.Eq (a,b) -> U.eq (convert_term a) (convert_term b)
      | FO.And l -> U.and_ (List.map convert_term l)
      | FO.Or l -> U.or_ (List.map convert_term l)
      | FO.Not f -> U.not_ (convert_term f)
      | FO.Imply (a,b) -> U.imply (convert_term a) (convert_term b)
      | FO.Equiv (a,b) -> U.eq (convert_term a) (convert_term b)
      | FO.Forall (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        U.forall v (convert_term t)
      | FO.Exists (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        U.exists v (convert_term t)
      | FO.Var v ->
        U.var (Var.update_ty v ~f:(convert_ty))
      | FO.Undefined t ->
        U.builtin (`Undefined_self (convert_term t))
      | FO.Undefined_atom (c,ty,l) ->
        let l = List.map convert_term l in
        U.app
          (U.builtin (`Undefined_atom (c,convert_top_ty ty)))
          l
      | FO.Unparsable ty ->
        U.unparsable ~ty:(convert_ty ty)
      | FO.Card_at_least (ty,n) ->
        U.card_at_least (convert_ty ty) n
      | FO.App (f,l) ->
        let l = List.map convert_term l in
        U.app (U.const f) l
      | FO.Mu (v,t) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        U.mu v (convert_term t)
      | FO.Fun (v,t) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        U.fun_ v (convert_term t)
      | FO.DataTest (c,t) ->
        U.app_builtin (`DataTest c) [convert_term t]
      | FO.DataSelect (c,n,t) ->
        U.app_builtin (`DataSelect (c,n)) [convert_term t]
      | FO.Let (v,t,u) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        U.let_ v (convert_term t) (convert_term u)
      | FO.Ite (a,b,c) ->
        U.ite (convert_term a) (convert_term b) (convert_term c)

  let convert_model m = Model.map m ~term:convert_term ~ty:convert_ty
end

module Make(T1 : TermInner.S) = struct
  module Conv = Of_ho(T1)
  module ConvBack = To_ho(T1)

  let pipe_with ~print ~decode =
    let on_encoded =
      Utils.singleton_if print ()
        ~f:(fun () ->
          Format.printf "@[<v2>@{<Yellow>after to_fo@}: {@,@[%a@]@,}@]@." FO.pp_problem)
    in
    Transform.make
      ~name:"to_fo"
      ~on_encoded
      ~encode:(fun pb ->
        let pb' = Conv.convert_problem pb in
        pb', ()
      )
      ~decode
      ()

  let pipe ~print () =
    pipe_with ~print
      ~decode:(fun _st -> Problem.Res.map_m ~f:ConvBack.convert_model)
end
