
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = ID
module Var = Var
module Sig = Signature
module TI = TermInner

module Builtin = TI.Builtin
module TyBuiltin = TI.TyBuiltin

module Binder = struct
  type t = [`Forall | `Exists | `Fun | `Mu]
  let lift
  : t -> TI.Binder.t
  = function
    | `Forall -> `Forall
    | `Exists -> `Exists
    | `Mu -> `Mu
    | `Fun -> `Fun
end

type id = ID.t
type 'a var = 'a Var.t

type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | Builtin of 'a Builtin.t (** built-in operation *)
  | Bind of Binder.t * 'a var * 'a
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a TI.cases (** shallow pattern-match *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a

(** The main signature already  contains every util, printer, constructors,
    equality, etc. because after that it would be impossible to use
    the equality [t = INNER.t]. *)
module type S = sig
  module T : TI.REPR
  type t = T.t

  val repr : T.t -> T.t view
end

(** Build a representation and all the associated utilities *)
module Make(T : TI.REPR)
: S with module T = T
= struct
  module T = T
  type t = T.t

  let repr t = match T.repr t with
    | TI.Const id -> Const id
    | TI.Var v -> Var v
    | TI.App (f,l) -> App (f,l)
    | TI.Builtin b -> Builtin b
    | TI.Bind (`TyForall,_,_)
    | TI.TyMeta _ -> assert false
    | TI.Bind ((`Forall | `Exists | `Fun | `Mu) as b,v,t) -> Bind(b,v,t)
    | TI.Let (v,t,u) -> Let(v,t,u)
    | TI.Match (t,l) -> Match (t,l)
    | TI.TyBuiltin b -> TyBuiltin b
    | TI.TyArrow (a,b) -> TyArrow(a,b)
end

module ToFO(T : TI.S) = struct
  module Subst = Var.Subst
  module P = TI.Print(T)
  module U = TI.Util(T)
  module Mono = Make(T)

  exception NotInFO of string

  let section = Utils.Section.make "to_fo"

  let () = Printexc.register_printer
    (function
      | NotInFO msg -> Some(Utils.err_sprintf "term_mono:@ %s" msg)
      | _ -> None
    )

  let fail_ msg = raise (NotInFO msg)
  let failf msg = Utils.exn_ksprintf ~f:fail_ msg

  let fail_ t msg =
    failf
    "@[<2>term `@[%a@]` is not in the first-order fragment:@ %s@]"
      P.print t msg

  let rec conv_ty t = match Mono.repr t with
    | Var _ -> fail_ t "variable in type"
    | TyBuiltin b ->
        begin match b with
        | `Prop -> FO.Ty.builtin `Prop
        | `Unitype -> FO.Ty.builtin `Unitype
        | `Kind -> fail_ t "kind belongs to HO fragment"
        | `Type -> fail_ t "type belongs to HO fragment"
        end
    | Const id -> FO.Ty.const id
    | App (f,l) ->
        begin match Mono.repr f with
        | Const id -> FO.Ty.app id (List.map conv_ty l)
        | _ -> fail_ t "non-constant application"
        end
    | TyArrow _ -> fail_ t "arrow in atomic type"
    | Let _
    | Match _
    | Builtin _
    | Bind _ -> fail_ t "not a type"

  let conv_var v = Var.update_ty ~f:conv_ty v

  (* find arguments *)
  let rec flat_arrow_ t = match Mono.repr t with
    | TyArrow (a, b) ->
        let args, ret = flat_arrow_ b in
        a :: args, ret
    | _ -> [], t

  let conv_top_ty t =
    let args, ret = flat_arrow_ t in
    let args = List.map (conv_ty ) args
    and ret = conv_ty ret in
    args, ret

  let rec conv_term ~sigma t = match Mono.repr t with
    | Const id -> FO.T.const id
    | Var v -> FO.T.var (conv_var v)
    | Let (v,t,u) ->
        FO.T.let_ (conv_var v) (conv_term ~sigma t) (conv_term ~sigma u)
    | Builtin (`Ite (a,b,c)) ->
        FO.T.ite
          (conv_term ~sigma a) (conv_term ~sigma b) (conv_term ~sigma c)
    | Builtin (`Undefined_self (c,t)) ->
        FO.T.undefined c (conv_term ~sigma t)
    | Builtin (`Undefined_atom (c,ty)) ->
        FO.T.undefined_atom c (conv_ty ty)
    | Builtin (`Unparsable ty) -> FO.T.unparsable (conv_ty ty)
    | Builtin `True -> FO.T.true_
    | Builtin `False -> FO.T.false_
    | Builtin (`Eq (a,b)) ->
        (* forbid equality between functions *)
        let ty = U.ty_exn ~sigma:(Sig.find ~sigma) a in
        begin match T.repr ty with
          | TI.TyArrow _
          | TI.Bind (`TyForall, _, _) -> fail_ t "equality between functions";
          | TI.TyBuiltin `Prop ->
            FO.T.equiv (conv_term ~sigma a) (conv_term ~sigma b)
          | _ ->
            FO.T.eq (conv_term ~sigma a) (conv_term ~sigma b)
        end
    | Builtin (`Not t) -> FO.T.not_ (conv_term ~sigma t)
    | Builtin (`And l) -> FO.T.and_ (List.map (conv_term ~sigma) l)
    | Builtin (`Or l) -> FO.T.or_ (List.map (conv_term ~sigma) l)
    | Builtin (`Imply (a,b)) ->
        FO.T.imply (conv_term ~sigma a) (conv_term ~sigma b)
    | App (f, l) ->
        begin match Mono.repr f, l with
        | Const id, _ -> FO.T.app id (List.map (conv_term ~sigma) l)
        | Builtin (`DataTest c), [t] ->
            FO.T.data_test c (conv_term ~sigma t)
        | Builtin (`DataSelect (c,n)), [t] ->
            FO.T.data_select c n (conv_term ~sigma t)
        | _ -> fail_ t "application of non-constant term"
        end
    | Bind (`Fun,v,t) ->
        FO.T.fun_ (conv_var v) (conv_term ~sigma t)
    | Bind (`Mu,v,t) ->
        FO.T.mu (conv_var v) (conv_term ~sigma t)
    | Bind (`Forall, v,f) ->
        FO.T.forall (conv_var v) (conv_term ~sigma f)
    | Bind (`Exists, v,f) ->
        FO.T.exists (conv_var v) (conv_term ~sigma f)
    | Match _ -> fail_ t "no case in FO terms"
    | Builtin (`Guard _) -> fail_ t "no guards (assert/assume) in FO"
    | Builtin (`DataSelect _ | `DataTest _) ->
        fail_ t "no unapplied data-select/test in FO"
    | TyBuiltin _
    | TyArrow (_,_) -> fail_ t "no types in FO terms"

  let conv_form ~sigma f =
    Utils.debugf 3 ~section
      "@[<2>convert to FO the formula@ `@[%a@]`@]" (fun k -> k P.print f);
    conv_term ~sigma f

  let convert_eqns
  : type inv.
    head:id -> sigma:T.t Sig.t -> (T.t,T.t,inv) Statement.equations -> FO.T.t list
  = fun ~head ~sigma eqns ->
    let module St = Statement in
    let conv_eqn (vars, args, rhs, side) =
      let vars = List.map conv_var vars in
      let lhs = FO.T.app head args in
      let f =
        if U.ty_returns_Prop (Sig.find_exn ~sigma head)
        then FO.T.equiv lhs (conv_term ~sigma rhs)
        else FO.T.eq lhs (conv_term ~sigma rhs)
      in
      (* add side conditions *)
      let side = List.map (conv_form ~sigma) side in
      let f = if side=[] then f else FO.T.imply (FO.T.and_ side) f in
      List.fold_right FO.T.forall vars f
    in
    match eqns with
    | St.Eqn_single (vars,rhs) ->
        (* [id = fun vars. rhs] *)
        let vars = List.map conv_var vars in
        [ FO.T.eq
            (FO.T.const head)
            (List.fold_right FO.T.fun_ vars (conv_term ~sigma rhs)) ]
    | St.Eqn_app (_,vars,lhs,rhs) ->
        (* [id = fun vars. rhs] *)
        let vars = List.map conv_var vars in
        let lhs = conv_term ~sigma lhs in
        let rhs = conv_term ~sigma rhs in
        [ List.fold_right FO.T.forall vars (FO.T.eq lhs rhs) ]
    | St.Eqn_nested l ->
        List.map
          (fun (vars,args,rhs,side) ->
            conv_eqn (vars, List.map (conv_term ~sigma) args, rhs, side))
          l

  let convert_statement ~sigma st =
    let module St = Statement in
    match St.view st with
    | St.Decl (id, ty, attrs) ->
        let _, _, ret = U.ty_unfold ty in
        let st' =
          if U.ty_is_Type ret
          then
            let n = U.ty_num_param ty in
            FO.TyDecl (id, n)
          else
            let ty = conv_top_ty ty in
            FO.Decl (id, ty)
        in
        (* additional statements, obtained from attributes *)
        let others =
          CCList.filter_map
            (function
              | St.Attr_card_max n -> Some (FO.CardBound (id, `Max, n))
              | St.Attr_card_min n -> Some (FO.CardBound (id, `Min, n))
              | St.Attr_infinite ->
                failf "@[<2>infinite type `%a`@ should have been eliminated@]" ID.print id
              | St.Attr_finite_approx _
              | St.Attr_infinite_upcast
              | St.Attr_abstract
              | St.Attr_incomplete
              | St.Attr_exn _ -> None)
            attrs
        in
        st' :: others
    | St.Axiom a ->
        let mk_ax x = FO.Axiom x in
        begin match a with
        | St.Axiom_std l ->
            List.map (fun ax -> conv_form  ~sigma ax |> mk_ax) l
        | St.Axiom_spec s ->
            (* first declare all types; then push axioms *)
            let decls = List.rev_map
              (fun def ->
                let ty = conv_top_ty def.St.defined_ty in
                let head = def.St.defined_head in
                FO.Decl (head, ty))
              s.St.spec_defined
            and ax = List.map
              (fun ax -> ax |> conv_form ~sigma |> mk_ax)
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
                  FO.Decl (head, ty))
                s
            and axioms =
              CCList.flat_map
                (fun def ->
                  (* transform equations *)
                  let head = def.St.rec_defined.St.defined_head in
                  let l = convert_eqns ~head ~sigma def.St.rec_eqns in
                  List.map mk_ax l)
                s
            in
            List.rev_append decls axioms
        end
    | St.Goal f ->
        [ FO.Goal (conv_form ~sigma f) ]
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
    let sigma = Problem.signature p in
    let res =
      CCVector.flat_map_list
        (convert_statement ~sigma)
        (Problem.statements p)
    in
    FO.Problem.make ~meta res
end

module OfFO(T:TI.S) = struct
  module U = TI.Util(T)
  type t = T.t

  let rec convert_ty t = match FO.Ty.view t with
    | FO.TyBuiltin b ->
        let b = match b with
          | `Prop -> `Prop
          | `Unitype -> `Unitype
        in U.ty_builtin b
    | FO.TyApp (f,l) ->
        let l = List.map convert_ty l in
        U.ty_app (U.ty_const f) l

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
    | FO.Undefined(c,t) ->
        U.builtin (`Undefined_self (c,convert_term t))
    | FO.Undefined_atom (c,ty) ->
        U.builtin (`Undefined_atom (c,convert_ty ty))
    | FO.Unparsable ty ->
        U.unparsable ~ty:(convert_ty ty)
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

module TransFO(T1 : TI.S) = struct
  module Conv = ToFO(T1)
  module ConvBack = OfFO(T1)

  let pipe_with ~print ~decode =
    let on_encoded =
      Utils.singleton_if print ()
        ~f:(fun () ->
          Format.printf "@[<v2>@{<Yellow>after to_fo@}: {@,@[%a@]@,}@]@." FO.print_problem)
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
