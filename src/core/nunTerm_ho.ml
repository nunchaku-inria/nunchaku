
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

(*$inject
  let pterm = NunLexer.HO.term_of_str_exn

  module Su = SubstUtil(Default)
*)

module ID = NunID
module Var = NunVar
module TyI = NunType_intf
module Sig = NunSignature

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

open NunTerm_intf

module type POLY_VIEW = sig
  include NunTerm_intf.VIEW

  module Ty : sig
    type 'i t = 'i ty
    val view : 'i t -> ('i t,'i) NunType_intf.view
  end
end

module type VIEW = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  type t
  type ty = t

  val view : t -> (t, invariant) NunTerm_intf.view

  module Ty : sig
    type t = ty
    val view : t -> (t,invariant) NunType_intf.view
  end
end

module type S = sig
  type invariant_poly
  type invariant_meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  val poly : invariant_poly NunMark.poly_witness

  type t
  type ty = t

  val view : t -> (t, invariant) NunTerm_intf.view
  val build : (t, invariant) NunTerm_intf.view -> t

  module Ty : NunType_intf.AS_TERM
    with type term = t and type t = ty
    and type invariant_poly = invariant_poly
    and type invariant_meta = invariant_meta

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val app_builtin : NunBuiltin.T.t -> t list -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val match_with : t -> t NunTerm_intf.cases -> t
  val ite : t -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t
  val eq : t -> t -> t

  val mk_bind : invariant_poly NunTerm_intf.binder -> Ty.t var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_kind : Ty.t (** Type of ty_type *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t
end

module type S_POLY = sig
  type invariant_meta
  include S
    with type invariant_poly = NunMark.polymorph
  and type invariant_meta := invariant_meta

  val ty_var : ty var -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
end

module Default_(I : sig type poly type meta end) = struct
  type invariant_poly = I.poly
  type invariant_meta = I.meta
  type invariant = <poly: invariant_poly; meta: invariant_meta>

  type t = {
    view: (t, invariant) view;
  }
  type ty = t

  (* special constants: kind and type *)
  let kind_ = {view=TyBuiltin NunBuiltin.Ty.Kind}
  let type_ = {view=TyBuiltin NunBuiltin.Ty.Type}
  let prop = {view=TyBuiltin NunBuiltin.Ty.Prop}

  let view t = t.view

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | App ({view=AppBuiltin (b, l1); _}, l2) ->
        make_raw_ (AppBuiltin (b, l1 @ l2))
    | _ -> make_raw_ view

  let app_builtin s l = build (AppBuiltin (s,l))
  let builtin s = app_builtin s []
  let const id = build (Const id)
  let var v = build (Var v)
  let app t l = build (App(t,l))
  let mk_bind (b:invariant_poly binder) v t = build (Bind (b,v,t))
  let fun_ v t = build (Bind (Fun,v, t))
  let let_ v t u = build (Let (v, t, u))
  let match_with t l =
    if ID.Map.is_empty l then invalid_arg "Term_ho.case: empty list of cases";
    build (Match (t,l))
  let ite a b c =
    app (builtin NunBuiltin.T.Ite) [a;b;c]
  let forall v t = build (Bind(Forall,v, t))
  let exists v t = build (Bind(Exists,v, t))
  let eq a b = app (builtin NunBuiltin.T.Eq) [a;b]

  let ty_type = type_
  let ty_kind = kind_
  let ty_prop = prop

  let ty_builtin b = build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l =
    if l=[] then f else app f l
  let ty_arrow a b = build (TyArrow (a,b))

  module Ty1 = struct
    type term = t
    type t = ty
    type invariant_meta = I.meta
    type invariant_poly = I.poly

    let is_Type t = match t.view with
      | TyBuiltin NunBuiltin.Ty.Type -> true
      | _ -> false

    let is_Kind t = match t.view with
      | TyBuiltin NunBuiltin.Ty.Kind -> true
      | _ -> false

    let rec returns (t:t) = match t.view with
      | TyArrow (_, t') -> returns t'
      | Bind (TyForall, _, t') -> returns t'
      | _ -> t

    let returns_Type t = match (returns t).view with
      | TyBuiltin NunBuiltin.Ty.Type -> true
      | _ -> false
  end
end

module DefaultMono
: S
  with type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta
= struct
  include Default_(struct
    type poly = M.monomorph
    type meta = M.without_meta
  end)

  let poly = M.Mono

  module Ty = struct
    include Ty1
    type invariant = <poly: invariant_poly; meta: invariant_meta>

    let view (t:t): (t,invariant) TyI.view = match t.view with
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | Var _
      | AppBuiltin _
      | Bind _
      | Match _
      | Let _ -> assert false

    let to_seq (t:t) yield =
      let rec aux (ty:t) =
        yield ty;
        match view ty with
        | TyI.Builtin _
        | TyI.Const _ -> ()
        | TyI.App (f,l) -> aux f; List.iter aux l
        | TyI.Arrow (a,b) -> aux a; aux b
      in
      aux t

    include TyI.Print(struct
      type invariant_meta = NunMark.without_meta
      type invariant_poly = NunMark.monomorph
      type invariant = <poly: invariant_poly; meta: invariant_meta>
      type t = ty
      let view = view
    end)
  end
end

module DefaultPoly
: S_POLY
  with type invariant_poly = NunMark.polymorph
  and type invariant_meta = NunMark.without_meta
= struct
  include Default_(struct
    type meta = M.without_meta
    type poly = M.polymorph
  end)

  let poly = M.Poly

  module Ty = struct
    include Ty1
    type invariant = <poly: invariant_poly; meta: invariant_meta>

    let view (t:t): (t,invariant) TyI.view = match t.view with
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | Var v -> TyI.Var v
      | Bind (TyForall, v, t) -> TyI.Forall (v,t)
      | AppBuiltin _
      | Bind _
      | Match _
      | Let _ -> assert false

    let to_seq t yield =
      let rec aux (ty:t) =
        yield ty;
        match view ty with
        | TyI.Builtin _
        | TyI.Const _ -> ()
        | TyI.App (f,l) -> aux f; List.iter aux l
        | TyI.Arrow (a,b) -> aux a; aux b
        | TyI.Var _ -> ()
        | TyI.Forall (_,t) -> aux t
      in
      aux t

    include TyI.Print(struct
      type invariant_meta = NunMark.without_meta
      type invariant_poly = NunMark.polymorph
      type invariant = <poly: invariant_poly; meta: invariant_meta>
      type t = ty
      let view = view
    end)
  end

  let ty_var v = var v
  let ty_forall a b = build (Bind(TyForall,a,b))
end

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

let default_poly =
  (module DefaultPoly : S with type t = DefaultPoly.t
  and type invariant_poly = NunMark.polymorph
  and type invariant_meta = NunMark.without_meta)

let default_mono =
  (module DefaultMono : S with type t = DefaultMono.t
  and type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta)

(** {2 Printing} *)

module type PRINT = sig
  type term
  type ty = term

  val print : term printer
  val print_in_app : term printer
  val print_in_binder : term printer

  val print_ty : ty printer
end

module Print(T : VIEW) = struct
  type term = T.t
  type ty = T.ty

  let fpf = Format.fprintf

  let pp_list_ ?(start="") ?(stop="") ~sep pp =
    CCFormat.list ~start ~stop ~sep pp

  let rec print out t = match T.view t with
    | TyBuiltin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Const id -> ID.print_no_id out id
    | TyMeta v -> NunMetaVar.print out v
    | Var v -> Var.print out v
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        fpf out "@[<2>if %a@ then %a@ else %a@]"
          print a print b print c
    | AppBuiltin (NunBuiltin.T.DataTest c, [t]) ->
        fpf out "@[<2>is-%a@ %a@]" ID.print_name c print t
    | AppBuiltin (NunBuiltin.T.DataSelect (c,n), [t]) ->
        fpf out "@[<2>select-%a-%d@ %a@]" ID.print_name c n print t
    | AppBuiltin (b, []) -> CCFormat.string out (NunBuiltin.T.to_string b)
    | AppBuiltin (f, [a;b]) when NunBuiltin.T.fixity f = `Infix ->
        fpf out "@[<hv>%a@ %s@ %a@]"
          print_in_app a (NunBuiltin.T.to_string f) print_in_app b
    | AppBuiltin (b,l) ->
        fpf out "@[<2>%s@ %a@]" (NunBuiltin.T.to_string b)
          (pp_list_ ~sep:" " print_in_app) l
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (pp_list_ ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print v print t print u
    | Match (t,l) ->
        let pp_case out (id,(vars,t)) =
          fpf out "@[<hv2>| %a %a ->@ %a@]"
            ID.print_name id (pp_list_ ~sep:" " Var.print) vars print t
        in
        fpf out "@[<hv2>match @[%a@] with@ %a end@]"
          print t (pp_list_ ~sep:"" pp_case) (ID.Map.to_list l)
    | Bind (b, v, t) ->
        let s = match b with
          | Fun -> "fun" | Forall -> "forall" | Exists -> "exists" | TyForall -> "pi"
        in
        fpf out "@[<2>%s %a:%a.@ %a@]" s Var.print v print_ty_in_app (Var.ty v) print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_ty_in_arrow a print_ty b

  and print_ty out ty = print out ty
  and print_ty_in_app out ty = print_in_app out ty
  and print_ty_in_arrow out ty = print_in_binder out ty

  and print_in_app out t = match T.view t with
    | AppBuiltin (_,[]) | TyBuiltin _ | Const _ -> print out t
    | TyMeta _ -> print out t
    | Var _ -> print out t
    | App (_,_) | AppBuiltin (_,_::_)
    | Bind _ | Let _ | Match _
    | TyArrow (_,_) -> fpf out "(@[%a@])" print t

  and print_in_binder out t = match T.view t with
    | TyBuiltin _ | Const _ | App (_,_) | AppBuiltin _ ->
        print out t
    | Var _ -> print out t
    | TyMeta _ -> print out t
    | Bind _ | Let _ | Match _ | TyArrow (_,_) -> fpf out "(@[%a@])" print t
end

(** {2 Utils with Substitutions} *)

exception Undefined of id

let () = Printexc.register_printer
  (function
    | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
    | _ -> None
  )

module SubstUtil(T : S)(Subst : Var.SUBST with type ty = T.ty) = struct
  type subst = T.Ty.t Subst.t

  let rec equal ~subst ty1 ty2 = match T.view ty1, T.view ty2 with
    | Const id1, Const id2 -> ID.equal id1 id2
    | Var v1, _ when Subst.mem ~subst v1 ->
        equal ~subst (Subst.find_exn ~subst v1) ty2
    | _, Var v2 when Subst.mem ~subst v2 ->
        equal ~subst ty1 (Subst.find_exn ~subst v2)
    | Var v1, Var v2 -> Var.equal v1 v2
    | AppBuiltin (b1,l1), AppBuiltin (b2,l2) ->
        NunBuiltin.T.equal b1 b2 &&
        List.length l1 = List.length l2 &&
        List.for_all2 (equal ~subst) l1 l2
    | TyBuiltin b1, TyBuiltin b2 -> NunBuiltin.Ty.equal b1 b2
    | TyMeta v1, TyMeta v2 -> NunMetaVar.equal v1 v2
    | App (f1,l1), App (f2, l2) ->
        equal ~subst f1 f2
          && List.length l1 = List.length l2
          && List.for_all2 (equal ~subst) l1 l2
    | TyArrow (a1,b1), TyArrow (a2,b2) ->
        equal ~subst a1 a2 && equal ~subst b1 b2
    | Bind (b1, v1, t1), Bind (b2, v2, t2) ->
        b1 = b2 &&
        ( let v = Var.fresh_copy v1 in
          let subst = Subst.add ~subst v1 (T.var v) in
          let subst = Subst.add ~subst v2 (T.var v) in
          equal ~subst t1 t2 )
    | Let (v1,t1,u1), Let (v2,t2,u2) ->
        let subst = Subst.add ~subst v1 t1 in
        let subst = Subst.add ~subst v2 t2 in
        equal ~subst u1 u2
    | Match (t1,l1), Match (t2,l2) ->
        ID.Map.cardinal l1 = ID.Map.cardinal l2 &&
        equal ~subst t1 t2 &&
        List.for_all2
          (fun (id1,(vars1,rhs1)) (id2,(vars2,rhs2)) ->
            assert (List.length vars1=List.length vars2);
            ID.equal id1 id2
            &&
            let subst = List.fold_right2
              (fun v1 v2 subst ->
                let v = Var.fresh_copy v1 in
                let subst = Subst.add ~subst v1 (T.var v) in
                let subst = Subst.add ~subst v2 (T.var v) in
                subst
              ) vars1 vars2 subst
            in
            equal ~subst rhs1 rhs2
          )
          (cases_to_list l1) (* list, sorted by ID *)
          (cases_to_list l2)
    | Var _, _
    | Match _, _
    | TyBuiltin _,_
    | AppBuiltin _,_
    | Const _,_
    | App (_,_),_
    | Bind _, _
    | Let (_,_,_),_
    | TyArrow (_,_),_ -> false
    | TyMeta _,_ -> false

  let rec deref ~subst t = match T.view t with
    | Var v ->
        begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
        end
    | _ -> t

  (* NOTE: when dependent types are added, substitution in types is needed *)

  let rec eval ~subst t = match T.view t with
    | TyMeta _ -> t
    | Const _
    | TyBuiltin _ -> t
    | AppBuiltin (_,[]) -> t
    | AppBuiltin (b,l) ->
        T.app_builtin b (List.map (eval ~subst) l)
    | Bind (b, v, t) ->
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (T.var v') in
        T.mk_bind b v' (eval ~subst t)
    | Let (v,t,u) ->
        let v' = Var.fresh_copy v in
        let t = eval ~subst t in
        let subst = Subst.add ~subst v (T.var v') in
        T.let_ v' t (eval ~subst u)
    | Match (t,l) ->
        let t = eval ~subst t in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let vars' = Var.fresh_copies vars in
            let subst = Subst.add_list ~subst vars (List.map T.var vars') in
            vars', eval ~subst rhs
          ) l
        in
        T.match_with t l
    | Var v ->
        begin try Subst.find_exn ~subst v
        with Not_found -> t
        end
    | App (f,l) ->
        T.app (eval ~subst f) (List.map (eval ~subst) l)
    | TyArrow (a,b) ->
        T.ty_arrow (eval ~subst a) (eval ~subst b)

  exception ApplyError of string * T.t * T.t list
  (** Raised when a type application fails *)

  exception UnifError of string * T.t * T.t
  (** Raised for unification or matching errors *)

  let () = Printexc.register_printer
    (function
      | ApplyError (msg, t, l) ->
          let module P = Print(T) in
          let msg = CCFormat.sprintf
            "@[<hv2>type error@ when applying %a@ on @[%a@]: %s@]"
              P.print_in_app t (CCFormat.list P.print_in_app) l msg
          in Some msg
      | UnifError (msg, t1, t2) ->
          let module P = Print(T) in
          let msg = CCFormat.sprintf
            "@[<hv2>unification error@ for %a@ and@ %a: %s@]"
              P.print_in_app t1 P.print_in_app t2 msg
          in Some msg
      | _ -> None
    )

  let error_apply_ msg ~hd ~l = raise (ApplyError (msg, hd, l))
  let error_unif_ msg t1 t2 = raise (UnifError (msg, t1, t2))

  let ty_apply_full t l =
    let rec app_ ~subst t l = match T.Ty.view t, l with
      | _, [] -> t, subst
      | TyI.Builtin _, _
      | TyI.App (_,_),_
      | TyI.Const _, _ ->
          error_apply_ "cannot apply this type" ~hd:t ~l
      | TyI.Var v, _ ->
          begin try
            let t = Subst.find_exn ~subst v in
            app_ ~subst t l
          with Not_found ->
            error_apply_ "cannot apply this type" ~hd:t ~l
          end
      | TyI.Meta _,_ -> assert false
      | TyI.Arrow (a, t'), b :: l' ->
          if equal ~subst a b
          then app_ ~subst t' l'
          else error_apply_ "type mismatch on first argument" ~hd:t ~l
      | TyI.Forall (v,t'), b :: l' ->
          let subst = Subst.add ~subst v b in
          app_ ~subst t' l'
    in
    app_ ~subst:Subst.empty t l

  let ty_apply t l =
    let t, subst = ty_apply_full t l in
    if Subst.is_empty subst then t else eval ~subst t

  let rec get_ty_arg_ ty i = match T.Ty.view ty with
    | TyI.App (_,_)
    | TyI.Builtin _
    | TyI.Const _ -> None
    | TyI.Var _ -> None
    | TyI.Meta _ -> None
    | TyI.Arrow (a,b) ->
        if i=0 then Some a else get_ty_arg_ b (i-1)
    | TyI.Forall (_,_) -> None

  type signature = T.ty Sig.t

  let rec ty_exn ~sigma (t:T.t) = match T.view t with
    | Const id ->
        begin try NunID.Map.find id sigma
        with Not_found -> raise (Undefined id)
        end
    | AppBuiltin (b,_) ->
        let module B = NunBuiltin.T in
        let prop1 = T.ty_arrow T.ty_prop T.ty_prop in
        let prop2 = T.ty_arrow T.ty_prop (T.ty_arrow T.ty_prop T.ty_prop) in
        begin match b with
          | B.Equiv
          | B.Imply
          | B.Or
          | B.And -> prop2
          | B.Not -> prop1
          | B.True
          | B.False
          | B.Ite
          | B.Eq -> T.ty_prop
          | B.DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = Sig.find_exn ~sigma id in
              T.ty_arrow (T.Ty.returns ty) T.ty_prop
          | B.DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = Sig.find_exn ~sigma id in
              begin match get_ty_arg_ ty n with
              | None ->
                  failwith "cannot infer type, wrong argument to DataSelect"
              | Some ty_arg ->
                  T.ty_arrow (T.Ty.returns ty) ty_arg
              end
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        ty_apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Bind (b,v,t) ->
        begin match b with
        | Forall
        | Exists -> T.ty_arrow (Var.ty v) T.ty_prop
        | Fun ->
            if T.Ty.returns_Type (Var.ty v)
            then match T.poly with
              | NunMark.Poly ->
                  (* FIXME: this branch should unify T.invariant_poly=polymorph,
                    but doesn't. Why? *)
                  T.build (Bind(Obj.magic TyForall, v, ty_exn ~sigma t))
              | NunMark.Mono ->
                  failwith "Term_ho.ty: polymorphic type"
            else T.ty_arrow (Var.ty v) (ty_exn ~sigma t)
        | TyForall -> T.ty_type
        end
    | Let (_,_,u) -> ty_exn ~sigma u
    | Match (_,m) ->
        let _, (_, rhs) = ID.Map.choose m in
        ty_exn ~sigma rhs
    | TyMeta _ -> assert false
    | TyBuiltin b ->
        begin match b with
        | NunBuiltin.Ty.Kind -> failwith "Term_ho.ty: kind has no type"
        | NunBuiltin.Ty.Type -> T.ty_kind
        | NunBuiltin.Ty.Prop -> T.ty_type
        end
    | TyArrow (_,_) -> T.ty_type

  let ty ~sigma t =
    try CCError.return (ty_exn ~sigma t)
    with e -> NunUtils.err_of_exn e

  (* return lists of same length, for
    unification or matching in the case of application *)
  let unif_l_ f1 l1 f2 l2 =
    let n1 = List.length l1 in
    let n2 = List.length l2 in
    if n1=n2 then f1::l1, f2::l2
    else if n1<n2 then
      let l2_1, l2_2 = CCList.take_drop (n2-n1) l2 in
      f1::l1, (T.app f2 l2_1) :: l2_2
    else
      let l1_1, l1_2 = CCList.take_drop (n1-n2) l1 in
      (T.app f1 l1_1) :: l1_2, f2 :: l2

  let match_exn ?(subst2=Subst.empty) t1 t2 =
    (* bound: bound variables in t1 and t2 *)
    let rec match_ subst t1 t2 =
      let t2 = deref ~subst:subst2 t2 in
      match T.view t1, T.view t2 with
      | AppBuiltin (b1,l1), AppBuiltin (b2,l2)
          when NunBuiltin.T.equal b1 b2 && List.length l1 = List.length l2 ->
            List.fold_left2 match_ subst l1 l2
      | Const id1, Const id2 when ID.equal id1 id2 -> subst
      | Var v1, _ ->
          begin match Subst.find ~subst v1 with
          | None ->
              (* NOTE: no occur check, we assume t1 and t2 share no variables *)
              Subst.add ~subst v1 t2
          | Some t1' ->
              if equal ~subst t1' t2
                then subst
                else error_unif_ "incompatible variable binding" t1 t2
          end
      | App (f1, l1), App (f2, l2) ->
          (* right-parenthesed application *)
          let l1, l2 = unif_l_ f1 l1 f2 l2 in
          List.fold_left2 match_ subst l1 l2
      | TyArrow (a1, b1), TyArrow (a2,b2) ->
          let subst = match_ subst a1 a2 in
          match_ subst b1 b2
      | Bind _, _
      | Let (_, _, _), _
      | Match _, _ -> invalid_arg "pattern is not first-order"
      | TyBuiltin b1, TyBuiltin b2 when NunBuiltin.Ty.equal b1 b2 -> subst
      | TyMeta _, _ -> assert false
      | AppBuiltin _, _
      | Const _, _
      | App (_, _), _
      | TyArrow _, _
      | TyBuiltin _, _ -> error_unif_ "do not match" t1 t2
    in
    match_ Subst.empty t1 t2

  let match_ ?subst2 t1 t2 =
    try Some (match_exn ?subst2 t1 t2)
    with UnifError _ -> None

  (* TODO write test *)
end

(** {2 Type Erasure} *)

module Erase(T : VIEW) = struct
  module Untyped = NunUntypedAST

  type ctx = {
    map: (string * int) ID.Tbl.t; (* remember results *)
    disamb: (string, int list) Hashtbl.t;  (* name -> set of nums *)
  }
  (* map ID to names, without collisions *)

  let create () = {
    map=ID.Tbl.create 32;
    disamb=Hashtbl.create 32;
  }

  (* find smallest int not in list *)
  let rec find_smallest_ n l =
    if List.mem n l then find_smallest_ (n+1) l else n

  (* find an identifier *)
  let find_ ~ctx id =
    try fst (ID.Tbl.find ctx.map id)
    with Not_found ->
      let name = ID.name id in
      let l = try Hashtbl.find ctx.disamb name with Not_found -> [] in
      let n = find_smallest_ 0 l in
      let name' = if n=0 then name else Printf.sprintf "%s/%d" name n in
      Hashtbl.replace ctx.disamb name (n::l);
      ID.Tbl.replace ctx.map id (name', n);
      name'

  (* remove an identifier *)
  let remove_ ~ctx id =
    let _, n = ID.Tbl.find ctx.map id in
    ID.Tbl.remove ctx.map id;
    let name = ID.name id in
    let l = Hashtbl.find ctx.disamb name in
    let l = CCList.Set.remove n l in
    if l=[]
    then Hashtbl.remove ctx.disamb name
    else Hashtbl.replace ctx.disamb name l

  (* enter the scope of [v] *)
  let enter_ ~ctx v f =
    let name = find_ ~ctx (Var.id v) in
    try
      let x = f name in
      remove_ ~ctx (Var.id v);
      x
    with e ->
      remove_ ~ctx (Var.id v);
      raise e

  let rec erase ~ctx t = match T.view t with
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        Untyped.ite (erase ~ctx a)(erase ~ctx b)(erase ~ctx c)
    | AppBuiltin (b,l) ->
        let module B = NunBuiltin.T in
        let b = match b with
          | B.True  -> Untyped.Builtin.True
          | B.False -> Untyped.Builtin.False
          | B.Not -> Untyped.Builtin.Not
          | B.Or -> Untyped.Builtin.Or
          | B.And -> Untyped.Builtin.And
          | B.Imply -> Untyped.Builtin.Imply
          | B.Equiv -> Untyped.Builtin.Equiv
          | B.Eq  -> Untyped.Builtin.Eq
          | B.DataSelect _
          | B.DataTest _
          | B.Ite -> assert false (* wrong arity: those are not terms *)
        in
        Untyped.app (Untyped.builtin b) (List.map (erase ~ctx) l)
    | Const id -> Untyped.var (find_ ~ctx id)
    | Var v -> Untyped.var (find_ ~ctx (Var.id v))
    | App (f,l) -> Untyped.app (erase ~ctx f) (List.map (erase ~ctx) l)
    | Bind (b,v,t) ->
        enter_typed_var_ ~ctx v
          (fun v' ->
            let t = erase ~ctx t in
            match b with
            | Fun -> Untyped.fun_ v' t
            | Forall -> Untyped.forall v' t
            | Exists -> Untyped.exists v' t
            | TyForall -> Untyped.ty_forall (fst v') t
          )
    | Let (v,t,u) ->
        let t = erase ~ctx t in
        enter_ ~ctx v
          (fun v' ->
            Untyped.let_ v' t (erase ~ctx u)
          )
    | Match _ -> assert false (* TODO *)
    | TyBuiltin b ->
        let b = match b with
          | NunBuiltin.Ty.Prop -> Untyped.Builtin.Prop
          | NunBuiltin.Ty.Type -> Untyped.Builtin.Type
          | NunBuiltin.Ty.Kind -> failwith "HO.erase: cannot erase Kind"
        in
        Untyped.builtin b
    | TyArrow (a,b) -> Untyped.ty_arrow (erase_ty ~ctx a) (erase_ty ~ctx b)
    | TyMeta _ -> assert false

  (* erase a type *)
  and erase_ty ~ctx t = erase ~ctx (t:T.ty:>T.t)

  (* enter a typed variable *)
  and enter_typed_var_ ~ctx v f =
    enter_ ~ctx v
      (fun v' ->
        let ty = erase_ty ~ctx (Var.ty v) in
        f (v', Some ty)
      )
end

module ToFO(T : S
  with type invariant_poly = NunMark.monomorph
  and type invariant_meta = NunMark.without_meta
)(FO : NunFO.S) = struct
  module Term = T (* alias for shadowing *)
  exception NotInFO of string * T.t

  type term = T.t
  type ty = T.ty

  let () = Printexc.register_printer
    (function
      | NotInFO (msg, t) ->
          let module P = Print(Term) in
          let msg = CCFormat.sprintf
            "@[<2>term `@[%a@]` is not in the first-order fragment:@ %s@]"
              P.print t msg
          in
          Some msg
      | _ -> None
    )

  module FOI = NunFO
  module Subst = Var.Subst(struct type t = T.ty end)

  let fail_ t msg = raise (NotInFO (msg, t))

  let rec conv_ty t = match T.Ty.view t with
    | TyI.Builtin b ->
        begin match b with
        | NunBuiltin.Ty.Prop -> FO.Ty.builtin FOI.TyBuiltin.Prop
        | NunBuiltin.Ty.Kind -> fail_ t "kind belongs to HO fragment"
        | NunBuiltin.Ty.Type -> fail_ t "type belongs to HO fragment"
        end
    | TyI.Const id -> FO.Ty.const id
    | TyI.App (f,l) ->
        begin match T.Ty.view f with
        | TyI.Const id -> FO.Ty.app id (List.map conv_ty l)
        | _ -> fail_ t "non-constant application"
        end
    | TyI.Arrow _ -> fail_ t "arrow in atomic type"

  let conv_var = Var.update_ty ~f:conv_ty

  (* find arguments *)
  let rec flat_arrow_ t = match T.Ty.view t with
    | TyI.Arrow (a, b) ->
        let args, ret = flat_arrow_ b in
        a :: args, ret
    | _ -> [], t

  let conv_top_ty t =
    let args, ret = flat_arrow_ t in
    let args = List.map conv_ty args
    and ret = conv_ty ret in
    args, ret

  let rec conv_term t = match T.view t with
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        FO.T.ite (conv_form_rec a) (conv_term b) (conv_term c)
    | AppBuiltin (NunBuiltin.T.DataTest c, [t]) ->
        FO.T.data_test c (conv_term t)
    | AppBuiltin (NunBuiltin.T.DataSelect (c,n), [t]) ->
        FO.T.data_select c n (conv_term t)
    | AppBuiltin _ -> fail_ t "no builtin in terms"
    | Const id -> FO.T.const id
    | Var v -> FO.T.var (conv_var v)
    | App (f,l) ->
        begin match T.view f with
        | Const id -> FO.T.app id (List.map conv_term l)
        | _ -> fail_ t "application of non-constant term"
        end
    | Bind (Fun,v,t) -> FO.T.fun_ (conv_var v) (conv_term t)
    | Bind ((Forall | Exists), _,_) -> fail_ t "no quantifiers in FO terms"
    | Let (v,t,u) ->
        FO.T.let_ (conv_var v) (conv_term t) (conv_term u)
    | Match _ -> fail_ t "no case in FO terms"
    | TyBuiltin _
    | TyArrow (_,_) -> fail_ t "no types in FO terms"

  and conv_form_rec t = match T.view t with
    | AppBuiltin (b,l) ->
        begin match b, l with
        | NunBuiltin.T.True, [] -> FO.Formula.true_
        | NunBuiltin.T.False, [] -> FO.Formula.false_
        | NunBuiltin.T.Not, [f] -> FO.Formula.not_ (conv_form_rec f)
        | NunBuiltin.T.Or, l -> FO.Formula.or_ (List.map conv_form_rec l)
        | NunBuiltin.T.And, l -> FO.Formula.and_ (List.map conv_form_rec l)
        | NunBuiltin.T.Imply, [a;b] ->
            FO.Formula.imply (conv_form_rec a) (conv_form_rec b)
        | NunBuiltin.T.Ite, [a;b;c] ->
            FO.Formula.f_ite
              (conv_form_rec a)(conv_form_rec b) (conv_form_rec c)
        | NunBuiltin.T.Equiv, [a;b] ->
            FO.Formula.equiv (conv_form_rec a)(conv_form_rec b)
        | NunBuiltin.T.Eq, [a;b] ->
            (* TODO: here use signature! maybe it's an equivalence *)
            FO.Formula.eq (conv_term a)(conv_term b)
        | NunBuiltin.T.DataSelect _, _
        | NunBuiltin.T.DataTest _, _ ->
            FO.Formula.atom (conv_term t)
        | _ -> assert false
        end
    | App _
    | Const _ -> FO.Formula.atom (conv_term t)
    | Var _ -> fail_ t "no variable in FO formulas"
    | Bind (Fun,v,t) ->
        FO.Formula.f_fun (conv_var v) (conv_form_rec t)
    | Bind (Forall, v,f) ->
        FO.Formula.forall (conv_var v) (conv_form_rec f)
    | Bind (Exists, v,f) ->
        FO.Formula.exists (conv_var v) (conv_form_rec f)
    | Let (v,t,u) ->
        FO.Formula.f_let
          (conv_var v) (conv_form_rec t) (conv_form_rec u)
    | Match _ -> fail_ t "no match in FO formulas"
    | TyArrow (_,_)
    | TyBuiltin _ -> fail_ t "no types in FO formulas"

  let conv_form f =
    let module P = Print(T) in
    NunUtils.debugf 3
      "@[<2>convert to FO the formula `@[%a@]`@]" (fun k -> k P.print f);
    conv_form_rec f

  (* does [ty] return prop? *)
  let returns_prop_ ty =
    let module TU = TyI.Utils(T.Ty) in
    match T.Ty.view (TU.returns ty) with
      | TyI.Builtin NunBuiltin.Ty.Prop -> true
      | _ -> false

  module SU = SubstUtil(T)(Subst)

  let convert_statement ~sigma (st:(_,_,M.linear) NunStatement.t) =
    let module St = NunStatement in
    match St.view st with
    | St.Decl (id, k, ty) ->
        begin match k with
        | St.Decl_type ->
            let args, _ = flat_arrow_ ty in
            let n = List.length args in
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
                  (fun eqn -> match eqn with
                  | St.Eqn_linear (vars,rhs) ->
                    let vars = List.map conv_var vars in
                    let args = List.map FO.T.var vars in
                    let lhs = FO.T.app head args in
                    let f =
                      if returns_prop_ (Sig.find_exn ~sigma head)
                      then
                        FO.Formula.equiv (FO.Formula.atom lhs) (conv_form rhs)
                      else FO.Formula.eq lhs (conv_term rhs)
                    in
                    let f = List.fold_right FO.Formula.forall vars f in
                    mk_ax f
                  )
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

module OfFO(T : S)(FO : NunFO.VIEW) = struct
  let rec convert_ty t = match FO.Ty.view t with
    | NunFO.TyBuiltin b ->
        let b = match b with
          | NunFO.TyBuiltin.Prop -> NunBuiltin.Ty.Prop
        in T.ty_builtin b
    | NunFO.TyApp (f,l) ->
        let l = List.map convert_ty l in
        T.ty_app (T.ty_const f) l

  and convert_term t =
    let module B = NunBuiltin.T in
    match FO.T.view t with
    | NunFO.Builtin b ->
        let b = match b with
          | NunFO.Builtin.Int _ -> NunUtils.not_implemented "conversion from int"
        in
        T.builtin b
    | NunFO.Var v ->
        T.var (Var.update_ty v ~f:convert_ty)
    | NunFO.App (f,l) ->
        let l = List.map convert_term l in
        T.app (T.const f) l
    | NunFO.Fun (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.fun_ v (convert_term t)
    | NunFO.DataTest (c,t) ->
        T.app_builtin (B.DataTest c) [convert_term t]
    | NunFO.DataSelect (c,n,t) ->
        T.app_builtin (B.DataSelect (c,n)) [convert_term t]
    | NunFO.Let (v,t,u) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.let_ v (convert_term t) (convert_term u)
    | NunFO.Ite (a,b,c) ->
        T.ite (convert_formula a) (convert_term b) (convert_term c)

  and convert_formula f =
    let module B = NunBuiltin.T in
    match FO.Formula.view f with
    | NunFO.Atom t -> convert_term t
    | NunFO.True -> T.builtin B.True
    | NunFO.False -> T.builtin B.False
    | NunFO.Eq (a,b) -> T.eq (convert_term a) (convert_term b)
    | NunFO.And l ->
        T.app (T.builtin B.And) (List.map convert_formula l)
    | NunFO.Or l ->
        T.app (T.builtin B.Or) (List.map convert_formula l)
    | NunFO.Not f ->
        T.app (T.builtin B.Not) [convert_formula f]
    | NunFO.Imply (a,b) ->
        T.app (T.builtin B.Imply) [convert_formula a; convert_formula b]
    | NunFO.Equiv (a,b) ->
        T.eq (convert_formula a) (convert_formula b)
    | NunFO.Forall (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.forall v (convert_formula t)
    | NunFO.Exists (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.exists v (convert_formula t)
    | NunFO.F_let (v,t,u) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.let_ v (convert_formula t) (convert_formula u)
    | NunFO.F_ite (a,b,c) ->
        T.ite (convert_formula a) (convert_formula b) (convert_formula c)
    | NunFO.F_fun (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.fun_ v (convert_formula t)

  let convert_t_or_f = function
    | NunFO.Term t -> convert_term t
    | NunFO.Form f -> convert_formula f

  let convert_model m = NunModel.map ~f:convert_t_or_f m
end

let to_fo (type a)(type b)(type c)(type d)
(module T : S with type t = a
    and type invariant_poly = NunMark.monomorph
    and type invariant_meta = NunMark.without_meta)
(module FO : NunFO.S with type T.t = b and type Ty.t = d and type formula = c) =
  let module Sol = NunSolver_intf in
  let module Conv = ToFO(T)(FO) in
  let module ConvBack = OfFO(T)(FO) in
  NunTransform.make1
  ~name:"to_fo"
  ~encode:(fun pb ->
    let pb' = Conv.convert_problem pb in
    pb', ()
  )
  ~decode:(fun _st m ->
    ConvBack.convert_model m
  )
  ()

let to_fo_no_model (type a)(type b)(type c)(type d)
(module T : S with type t = a
    and type invariant_poly = NunMark.monomorph
    and type invariant_meta = NunMark.without_meta)
(module FO : NunFO.S with type T.t = b and type Ty.t = d and type formula = c) =
  let module Conv = ToFO(T)(FO) in
  NunTransform.make1
  ~name:"to_fo"
  ~encode:(fun pb ->
    let pb' = Conv.convert_problem pb in
    pb', ()
  )
  ~decode:(fun _ x -> x)
  ()

(** {2 Conversion} *)

module Convert(T1 : VIEW)(T2 : S
  with type invariant_poly=T1.invariant_poly
  and type invariant_meta=T1.invariant_meta
) = struct
  let rec convert t = match T1.view t with
    | AppBuiltin (b,l) -> T2.app_builtin b (List.map convert l)
    | Const id -> T2.const id
    | Var v -> T2.var (aux_var v)
    | App (f,l) -> T2.app (convert f) (List.map convert l)
    | Bind (b,v,t) -> T2.mk_bind b (aux_var v) (convert t)
    | Let (v,t,u) -> T2.let_ (aux_var v) (convert t) (convert u)
    | Match (t,l) ->
        T2.match_with
          (convert t)
          (ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, convert rhs) l)
    | TyBuiltin b -> T2.ty_builtin b
    | TyArrow (a,b) -> T2.ty_arrow (convert a)(convert b)
    | TyMeta _ -> assert false

  and aux_var v = Var.update_ty ~f:convert v
end

(** {2 Conversion of UntypedAST to HO, without Type-Checking} *)

module OfUntyped(T : S_POLY) = struct
  module A = NunUntypedAST
  module Loc = NunLocation

  exception Error of A.term * string

  let () = Printexc.register_printer
    (function
      | Error (t,s) ->
          Some (CCFormat.sprintf "of_untyped: error on %a: %s" A.print_term t s)
      | _ -> None
    )

  let error_ t s = raise (Error (t,s))

  type env_cell =
    | ID of ID.t
    | Var of T.t Var.t

  let convert_term t =
    let env = Hashtbl.create 32 in
    let rec aux t = match Loc.get t with
      | A.App (f, l) ->
          T.app (aux f) (List.map aux l)
      | A.Wildcard -> error_ t "wildcard not supported"
      | A.Builtin b ->
          let module B = NunBuiltin in
          begin match b with
          | A.Builtin.Prop -> T.ty_prop
          | A.Builtin.Type -> T.ty_type
          | A.Builtin.Not -> T.ty_builtin B.Ty.Prop
          | A.Builtin.And -> T.builtin B.T.And
          | A.Builtin.Or -> T.builtin B.T.Or
          | A.Builtin.True -> T.builtin B.T.True
          | A.Builtin.False -> T.builtin B.T.False
          | A.Builtin.Imply -> T.builtin B.T.Imply
          | A.Builtin.Eq | A.Builtin.Equiv ->
              error_ t "unapplied equality"
          end
      | A.AtVar s
      | A.Var s ->
          begin try
            match Hashtbl.find env s with
            | ID id -> T.const id
            | Var v -> T.var v
          with Not_found ->
            (* constant, not variable *)
            let id = ID.make ~name:s in
            Hashtbl.add env s (ID id);
            T.const id
          end
      | A.MetaVar _ -> error_ t "meta variable"
      | A.Exists ((_, None), _)
      | A.Forall ((_, None), _)
      | A.Fun ((_, None), _) -> error_ t "untyped variable"
      | A.Fun ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> T.fun_ v (aux t))
      | A.Let _ ->
          error_ t "`let` unsupported (no way of inferring the type)"
      | A.Match _ ->
          error_ t "`match` unsupported (no way of inferring the type of variables)"
      | A.Ite (a,b,c) -> T.ite (aux a) (aux b) (aux c)
      | A.Forall ((v,Some ty),t) ->
          enter_var_ ~ty v (fun v -> T.forall v (aux t))
      | A.Exists ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> T.exists v (aux t))
      | A.TyArrow (a,b) -> T.ty_arrow (aux a) (aux b)
      | A.TyForall (v,t) ->
          enter_var_ ~ty:(A.builtin A.Builtin.Type) v (fun v -> T.ty_forall v (aux t))

    (* enter scope of [s] *)
    and enter_var_ s ~ty f =
      let ty = aux ty in
      let v = Var.make ~name:s ~ty in
      Hashtbl.add env s (Var v);
      let x = f v in
      Hashtbl.remove env s;
      x
    in
    aux t
end
