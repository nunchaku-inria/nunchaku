
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = NunID
module Var = NunVar
module Sig = NunSignature
module TI = NunTermInner

module Builtin = TI.Builtin
module TyBuiltin = TI.TyBuiltin

module Binder = struct
  type t = [`Forall | `Exists | `Fun]
  let lift
  : t -> TI.Binder.t
  = function
    | `Forall -> `Forall
    | `Exists -> `Exists
    | `Fun -> `Fun
end

type id = ID.t
type 'a var = 'a Var.t

type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | AppBuiltin of Builtin.t * 'a list (** built-in operation *)
  | Bind of Binder.t * 'a var * 'a
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a TI.cases (** shallow pattern-match *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a

type 't repr = 't -> 't view
(** A concrete representation of terms by the type [t'] *)

type 't build = 't view -> 't
(** A builder for a concrete representation with type ['t]. *)

let lift_repr_ = function
  | Const id -> TI.Const id
  | Var v -> TI.Var v
  | App (f,l) -> TI.App (f,l)
  | AppBuiltin (b,l) -> TI.AppBuiltin(b,l)
  | Bind (b,v,t) -> TI.Bind(Binder.lift b,v,t)
  | Let (v,t,u) -> TI.Let(v,t,u)
  | Match (t,l) -> TI.Match (t,l)
  | TyBuiltin b -> TI.TyBuiltin b
  | TyArrow (a,b) -> TI.TyArrow (a,b)

module type REPR = sig
  type t
  val repr : t repr
end

module type BUILD = sig
  type t
  val build : t build
end

(** The main signature already  contains every util, printer, constructors,
    equality, etc. because after that it would be impossible to use
    the equality [t = INNER.t]. *)
module type S = sig
  module INNER : TI.S
  type t = private INNER.t

  include REPR with type t := t
  include BUILD with type t := t

  include TI.UTIL with type t_ := t
  include TI.PRINT with type t := t
  val ty_meta : [`Not_available]
  val ty_var : [`Not_available]
  val ty_forall : [`Not_available]

  val of_inner_unsafe : INNER.t -> t
  (** Careful, this is totally unsafe and will result in [assert false] at
    some point if not properly used *)
end

(** Build a representation and all the associated utilities *)
module Make(T : TI.S)
: S with module INNER = T
= struct
  module INNER = T

  type t = T.t

  let repr t = match T.repr t with
    | TI.Const id -> Const id
    | TI.Var v -> Var v
    | TI.App (f,l) -> App (f,l)
    | TI.AppBuiltin (b,l) -> AppBuiltin(b,l)
    | TI.Bind (`TyForall,_,_)
    | TI.TyMeta _ -> assert false
    | TI.Bind ((`Forall | `Exists | `Fun) as b,v,t) -> Bind(b,v,t)
    | TI.Let (v,t,u) -> Let(v,t,u)
    | TI.Match (t,l) -> Match (t,l)
    | TI.TyBuiltin b -> TyBuiltin b
    | TI.TyArrow (a,b) -> TyArrow(a,b)

  let build v = T.build (lift_repr_ v)

  include TI.Util(T)

  include (TI.Print(T) : TI.PRINT with type t := t)

  let of_inner_unsafe t = t

  (* overload those operations: we cannot hide it without copying all the
     TI.UTIL signature, minus one operation *)
  let ty_meta = `Not_available
  let ty_var = `Not_available
  let ty_forall = `Not_available
end

(** {2 Default Representation}

  As a private alias to the default {!NunTermInner} representation, basically
  removing the meta case *)

module Default = Make(TI.Default)

module LiftRepr(T : REPR)
: TI.REPR with type t = T.t
= struct
  type t = T.t
  let repr t = lift_repr_ (T.repr t)
end

module ToFO(T : REPR)(FO : NunFO.S) = struct
  exception NotInFO of string * T.t


  module FOI = NunFO
  module Subst = Var.Subst
  module P = TI.Print(LiftRepr(T))
  module U = TI.UtilRepr(LiftRepr(T))

  let () = Printexc.register_printer
    (function
      | NotInFO (msg, t) ->
          let msg = CCFormat.sprintf
            "@[<2>term `@[%a@]` is not in the first-order fragment:@ %s@]"
              P.print t msg
          in
          Some msg
      | _ -> None
    )

  let fail_ t msg = raise (NotInFO (msg, t))

  let rec conv_ty t = match T.repr t with
    | Var _ -> fail_ t "variable in type"
    | TyBuiltin b ->
        begin match b with
        | `Prop -> FO.Ty.builtin `Prop
        | `Kind -> fail_ t "kind belongs to HO fragment"
        | `Type -> fail_ t "type belongs to HO fragment"
        end
    | Const id -> FO.Ty.const id
    | App (f,l) ->
        begin match T.repr f with
        | Const id -> FO.Ty.app id (List.map conv_ty l)
        | _ -> fail_ t "non-constant application"
        end
    | TyArrow _ -> fail_ t "arrow in atomic type"
    | Let _
    | Match _
    | AppBuiltin _
    | Bind _ -> fail_ t "not a type"

  let conv_var v = Var.update_ty ~f:conv_ty v

  (* find arguments *)
  let rec flat_arrow_ t = match T.repr t with
    | TyArrow (a, b) ->
        let args, ret = flat_arrow_ b in
        a :: args, ret
    | _ -> [], t

  let conv_top_ty t =
    let args, ret = flat_arrow_ t in
    let args = List.map (conv_ty ) args
    and ret = conv_ty ret in
    args, ret

  let rec conv_term t =
    let rec aux t = match T.repr t with
    | AppBuiltin (`Ite, [a;b;c]) ->
        FO.T.ite (conv_form_rec a) (aux b) (aux c)
    | AppBuiltin (`DataTest c, [t]) ->
        FO.T.data_test c (aux t)
    | AppBuiltin (`DataSelect (c,n), [t]) ->
        FO.T.data_select c n (aux t)
    | AppBuiltin _ -> fail_ t "no builtin in terms"
    | Const id -> FO.T.const id
    | Var v -> FO.T.var (conv_var v)
    | App (f,l) ->
        begin match T.repr f with
        | Const id -> FO.T.app id (List.map aux l)
        | _ -> fail_ t "application of non-constant term"
        end
    | Bind (`Fun,v,t) -> FO.T.fun_ (conv_var v) (aux t)
    | Bind ((`Forall | `Exists), _,_) -> fail_ t "no quantifiers in FO terms"
    | Let (v,t,u) ->
        FO.T.let_ (conv_var v) (aux t) (aux u)
    | Match _ -> fail_ t "no case in FO terms"
    | TyBuiltin _
    | TyArrow (_,_) -> fail_ t "no types in FO terms"
    in
    aux t

  and conv_form_rec t =
    let rec aux t = match T.repr t with
    | AppBuiltin (b,l) ->
        begin match b, l with
        | `True, [] -> FO.Formula.true_
        | `False, [] -> FO.Formula.false_
        | `Not, [f] -> FO.Formula.not_ (aux f)
        | `Or, l -> FO.Formula.or_ (List.map aux l)
        | `And, l -> FO.Formula.and_ (List.map aux l)
        | `Imply, [a;b] ->
            FO.Formula.imply (aux a) (aux b)
        | `Ite, [a;b;c] ->
            FO.Formula.f_ite
              (aux a)(aux b) (aux c)
        | `Equiv, [a;b] ->
            FO.Formula.equiv (aux a)(aux b)
        | `Eq, [a;b] ->
            (* TODO: here use signature! maybe it's an equivalence *)
            FO.Formula.eq (conv_term a)(conv_term b)
        | `DataSelect _, _
        | `DataTest _, _ ->
            FO.Formula.atom (conv_term t)
        | _ -> assert false
        end
    | App _
    | Const _ -> FO.Formula.atom (conv_term t)
    | Var _ -> fail_ t "no variable in FO formulas"
    | Bind (`Fun,v,t) ->
        FO.Formula.f_fun (conv_var v) (aux t)
    | Bind (`Forall, v,f) ->
        FO.Formula.forall (conv_var v) (aux f)
    | Bind (`Exists, v,f) ->
        FO.Formula.exists (conv_var v) (aux f)
    | Let (v,t,u) ->
        FO.Formula.f_let
          (conv_var v) (aux t) (aux u)
    | Match _ -> fail_ t "no match in FO formulas"
    | TyArrow (_,_)
    | TyBuiltin _ -> fail_ t "no types in FO formulas"
    in
    aux t

  let conv_form f =
    NunUtils.debugf 3
      "@[<2>convert to FO the formula `@[%a@]`@]" (fun k -> k P.print f);
    conv_form_rec f

  (* does [ty] return prop? *)
  let returns_prop_ t =
    match T.repr t with
      | TyBuiltin `Prop -> true
      | _ -> false

  let convert_eqn
  : type inv.
    head:id -> sigma:T.t Sig.t -> (T.t,T.t,inv) NunStatement.equation -> FO.formula
  = fun ~head ~sigma eqn ->
    let module St = NunStatement in
    let vars, args, rhs, side = match eqn with
      | St.Eqn_linear (vars,rhs,side) ->
          vars, List.map (fun v -> FO.T.var (conv_var v)) vars, rhs, side
      | St.Eqn_nested (vars,args,rhs,side) ->
          vars, List.map (conv_term) args, rhs, side
    in
    let vars = List.map (conv_var) vars in
    let lhs = FO.T.app head args in
    let f =
      if returns_prop_ (Sig.find_exn ~sigma head)
      then
        FO.Formula.equiv
          (FO.Formula.atom lhs)
          (conv_form rhs)
      else FO.Formula.eq lhs (conv_term rhs)
    in
    (* add side conditions *)
    let side = FO.Formula.and_ (List.map (conv_form) side) in
    let f = FO.Formula.imply side f in
    List.fold_right FO.Formula.forall vars f

  let convert_statement ~sigma st =
    let module St = NunStatement in
    match St.view st with
    | St.Decl (id, k, ty) ->
        begin match k with
        | St.Decl_type ->
            let n = U.ty_num_param ty in
            [ FOI.TyDecl (id, n) ]
        | St.Decl_fun ->
            let ty = conv_top_ty ty in
            [ FOI.Decl (id, ty) ]
        | St.Decl_prop ->
            let ty = conv_top_ty ty in
            [ FOI.Decl (id, ty) ]
        end
    | St.Axiom a ->
        let mk_ax x = FOI.Axiom x in
        begin match a with
        | St.Axiom_std l ->
            List.map (fun ax -> conv_form ax |> mk_ax) l
        | St.Axiom_spec s ->
            List.map
              (fun ax -> ax |> conv_form |> mk_ax)
              s.St.spec_axioms
        | St.Axiom_rec s ->
            CCList.flat_map
              (fun def ->
                let head = def.St.rec_defined.St.defined_head in
                List.map
                  (fun e -> mk_ax (convert_eqn ~head ~sigma e))
                  def.St.rec_eqns
              )
              s
        end
    | St.Goal f ->
        [ FOI.Goal (conv_form f) ]
    | St.TyDef (k, l) ->
        let convert_cstor c =
          {FOI.
            cstor_name=c.St.cstor_name;
            cstor_args=List.map (conv_ty) c.St.cstor_args;
          }
        in
        (* gather all variables *)
        let tys_vars =
          CCList.flat_map (fun tydef -> List.map Var.id tydef.St.ty_vars) l
        (* convert declarations *)
        and tys_defs = List.map
          (fun tydef ->
            let id = tydef.St.ty_id in
            let cstors = List.map convert_cstor tydef.St.ty_cstors in
            {FOI.ty_name=id; ty_cstors=cstors; }
          ) l
        in
        let l = {FOI.tys_vars; tys_defs; } in
        [ FOI.MutualTypes (k, l) ]

  let convert_problem p =
    let res = CCVector.create() in
    let sigma = NunProblem.signature p in
    CCVector.iter
      (fun st ->
        let l = convert_statement ~sigma st in
        CCVector.append_seq res (Sequence.of_list l)
      )
      (NunProblem.statements p);
    res |> CCVector.freeze |> FOI.Problem.make
end

module OfFO(T:S)(FO : NunFO.VIEW) = struct
  type t = T.t

  let rec convert_ty t = match FO.Ty.view t with
    | NunFO.TyBuiltin b ->
        let b = match b with
          | `Prop -> `Prop
        in T.ty_builtin b
    | NunFO.TyApp (f,l) ->
        let l = List.map convert_ty l in
        T.ty_app (T.ty_const f) l

  let rec convert_term t =
    match FO.T.view t with
    | NunFO.Builtin b ->
        let b = match b with
          | `Int _ -> NunUtils.not_implemented "conversion from int"
        in
        T.builtin b
    | NunFO.Var v ->
        T.var (Var.update_ty v ~f:(convert_ty))
    | NunFO.App (f,l) ->
        let l = List.map convert_term l in
        T.app (T.const f) l
    | NunFO.Fun (v,t) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        T.fun_ v (convert_term t)
    | NunFO.DataTest (c,t) ->
        T.app_builtin (`DataTest c) [convert_term t]
    | NunFO.DataSelect (c,n,t) ->
        T.app_builtin (`DataSelect (c,n)) [convert_term t]
    | NunFO.Let (v,t,u) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        T.let_ v (convert_term t) (convert_term u)
    | NunFO.Ite (a,b,c) ->
        T.ite (convert_formula a) (convert_term b) (convert_term c)

  and convert_formula f =
    match FO.Formula.view f with
    | NunFO.Atom t -> convert_term t
    | NunFO.True -> T.builtin `True
    | NunFO.False -> T.builtin `False
    | NunFO.Eq (a,b) -> T.eq (convert_term a) (convert_term b)
    | NunFO.And l ->
        T.app (T.builtin `And) (List.map convert_formula l)
    | NunFO.Or l ->
        T.app (T.builtin `Or) (List.map convert_formula l)
    | NunFO.Not f ->
        T.app (T.builtin `Not) [convert_formula f]
    | NunFO.Imply (a,b) ->
        T.app (T.builtin `Imply) [convert_formula a; convert_formula b]
    | NunFO.Equiv (a,b) ->
        T.eq (convert_formula a) (convert_formula b)
    | NunFO.Forall (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        T.forall v (convert_formula t)
    | NunFO.Exists (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        T.exists v (convert_formula t)
    | NunFO.F_let (v,t,u) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        T.let_ v (convert_formula t) (convert_formula u)
    | NunFO.F_ite (a,b,c) ->
        T.ite (convert_formula a) (convert_formula b) (convert_formula c)
    | NunFO.F_fun (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        T.fun_ v (convert_formula t)
  and convert_formula_ty = convert_ty

  let convert_t_or_f = function
    | NunFO.Term t -> convert_term t
    | NunFO.Form f -> convert_formula f

  let convert_model m = NunModel.map ~f:(convert_t_or_f) m
end

module TransFO(T1 : S)(T2 : NunFO.S) = struct
  module Conv = ToFO(T1)(T2)
  module ConvBack = OfFO(T1)(T2)

  let pipe () =
    NunTransform.make1
    ~name:"to_fo"
    ~encode:(fun pb ->
      let pb' = Conv.convert_problem pb in
      pb', ()
    )
    ~decode:(fun _st m -> ConvBack.convert_model m)
    ()

  let pipe_with ~decode =
    NunTransform.make1
    ~name:"to_fo"
    ~encode:(fun pb ->
      let pb' = Conv.convert_problem pb in
      pb', ()
    )
    ~decode:(fun _ x -> decode x)
    ()
end
