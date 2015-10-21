
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

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

open NunTerm_intf

module type VIEW = sig
  include NunTerm_intf.VIEW

  module Ty : sig
    type t = ty
    val view : t -> t NunType_intf.view
  end
end

module type S = sig
  include NunTerm_intf.VIEW

  module Ty : NunType_intf.AS_TERM with type term = t and type t = ty

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val app_builtin : NunBuiltin.T.t -> t list -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val ite : t -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t
  val eq : t -> t -> t

  val mk_bind : NunTerm_intf.binder -> Ty.t var -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_kind : Ty.t (** Type of ty_type *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : NunBuiltin.Ty.t -> Ty.t
  val ty_const : id -> Ty.t
  val ty_var : ty var -> Ty.t
  val ty_app : Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ty var -> Ty.t -> Ty.t
  val ty_arrow : Ty.t -> Ty.t -> Ty.t
end

module Default : S = struct
  type t = {
    view: t view;
  }
  type ty = t

  (* special constants: kind and type *)
  let kind_ = {view=TyBuiltin NunBuiltin.Ty.Kind}
  let type_ = {view=TyBuiltin NunBuiltin.Ty.Type}
  let prop = {view=TyBuiltin NunBuiltin.Ty.Prop}

  let view t = t.view

  let make_raw_ view = { view}

  let make_ view = match view with
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  let app_builtin s l = make_ (AppBuiltin (s,l))
  let builtin s = app_builtin s []
  let const id = make_ (Const id)
  let var v = make_ (Var v)
  let app t l = match t.view, l with
    | _, [] -> t
    | AppBuiltin (b, l1), _ -> app_builtin b (l1@l)
    | _ -> make_ (App (t, l))
  let mk_bind b v t = make_ (Bind (b,v,t))
  let fun_ v t = make_ (Bind (Fun,v, t))
  let let_ v t u = make_ (Let (v, t, u))
  let ite a b c =
    app (builtin NunBuiltin.T.Ite) [a;b;c]
  let forall v t = make_ (Bind(Forall,v, t))
  let exists v t = make_ (Bind(Exists,v, t))
  let eq a b = app (builtin NunBuiltin.T.Eq) [a;b]

  let ty_type = type_
  let ty_kind = kind_
  let ty_prop = prop

  let ty_builtin b = make_ (TyBuiltin b)
  let ty_const id = const id
  let ty_var v = var v
  let ty_app f l =
    if l=[] then f else app f l
  let ty_arrow a b = make_ (TyArrow (a,b))
  let ty_forall a b = make_ (Bind(TyForall,a,b))

  module Ty = struct
    type term = t
    type t = ty

    let view t = match t.view with
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | Var v -> TyI.Var v
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | Bind(TyForall,v,t) -> TyI.Forall (v,t)
      | TyMeta _ -> assert false
      | AppBuiltin _
      | Bind _
      | Let _ -> assert false

    let is_Type t = match t.view with
      | TyBuiltin NunBuiltin.Ty.Type -> true
      | _ -> false

    let is_Kind t = match t.view with
      | TyBuiltin NunBuiltin.Ty.Kind -> true
      | _ -> false

    let rec returns t = match t.view with
      | TyArrow (_, t')
      | Bind (TyForall, _, t') -> returns t'
      | _ -> t

    let returns_Type t = match (returns t).view with
      | TyBuiltin NunBuiltin.Ty.Type -> true
      | _ -> false

    let to_seq t yield =
      let rec aux ty =
        yield ty;
        match view ty with
        | TyI.Builtin _
        | TyI.Const _
        | TyI.Var _
        | TyI.Meta _ -> ()
        | TyI.App (f,l) -> aux f; List.iter aux l
        | TyI.Arrow (a,b) -> aux a; aux b
        | TyI.Forall (_,t) -> aux t
      in
      aux t

    include TyI.Print(struct type t = ty let view = view end)
  end
end

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

let default = (module Default : S with type t = Default.t)

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

  let rec print out t = match T.view t with
    | TyBuiltin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Const id -> ID.print_no_id out id
    | TyMeta v -> NunMetaVar.print out v
    | Var v -> Var.print out v
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        fpf out "@[<2>if %a@ then %a@ else %a@]"
          print a print b print c
    | AppBuiltin (b, []) -> CCFormat.string out (NunBuiltin.T.to_string b)
    | AppBuiltin (f, [a;b]) when NunBuiltin.T.fixity f = `Infix ->
        fpf out "@[<hv>%a@ %s %a@]"
          print_in_app a (NunBuiltin.T.to_string f) print_in_app b
    | AppBuiltin (b,l) ->
        fpf out "@[<2>%s@ %a@]" (NunBuiltin.T.to_string b)
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print v print t print u
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
    | AppBuiltin (_,[]) | TyBuiltin _ | Var _ | Const _ | TyMeta _ ->
        print out t
    | App (_,_) | AppBuiltin (_,_::_)
    | Bind _ | Let _
    | TyArrow (_,_) -> fpf out "@[(%a)@]" print t

  and print_in_binder out t = match T.view t with
    | TyBuiltin _ | Var _
    | Const _ | TyMeta _ | App (_,_) | AppBuiltin _ ->
        print out t
    | Bind _
    | Let _
    | TyArrow (_,_) -> fpf out "@[(%a)@]" print t
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
          let subst = Subst.add ~subst v1 (T.ty_var v) in
          let subst = Subst.add ~subst v2 (T.ty_var v) in
          equal ~subst t1 t2 )
    | Let (v1,t1,u1), Let (v2,t2,u2) ->
        let subst = Subst.add ~subst v1 t1 in
        let subst = Subst.add ~subst v2 t2 in
        equal ~subst u1 u2
    | Var _, _
    | TyBuiltin _,_
    | AppBuiltin _,_
    | Const _,_
    | TyMeta _,_
    | App (_,_),_
    | Bind _, _
    | Let (_,_,_),_
    | TyArrow (_,_),_ -> false

  let rec deref ~subst t = match T.view t with
    | Var v ->
        begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
        end
    | _ -> t

  (* NOTE: when dependent types are added, substitution in types is needed *)

  let rec eval ~subst t = match T.view t with
    | TyMeta _
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

  type signature = T.ty NunProblem.Signature.t

  let rec ty_exn ~sigma t = match T.view t with
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
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        ty_apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Bind (b,v,t) ->
        begin match b with
        | Forall
        | Exists -> T.ty_arrow (Var.ty v) T.ty_prop
        | Fun  ->
            if T.Ty.returns_Type (Var.ty v)
            then T.ty_forall v (ty_exn ~sigma t)
            else T.ty_arrow (Var.ty v) (ty_exn ~sigma t)
        | TyForall -> T.ty_type
        end
    | Let (_,_,u) -> ty_exn ~sigma u
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
      | Let (_, _, _), _ -> invalid_arg "pattern is not first-order"
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
          | B.Ite -> assert false
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

module AsFO(T : S) = struct
  module Term = T (* alias for shadowing *)
  exception NotInFO of string * T.t

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
  module Subst = Var.Subst(T)
  module SubstUtil = SubstUtil(T)(Subst)

  let fail t msg = raise (NotInFO (msg, t))

  module Ty = struct
    type t = T.t
    type toplevel_ty = t list * t

    let view t = match T.view t with
      | AppBuiltin _ -> fail t "builtin term"
      | Const id -> FOI.TyApp (id, [])
      | Var _ -> fail t "variable in type"
      | App (f,l) ->
          begin match T.view f with
          | Const id -> FOI.TyApp (id, l)
          | _ -> fail t "non-constant application"
          end
      | Bind (TyForall, _, _) -> fail t "no quantification in FO types"
      | Bind (Fun,_,_) -> fail t "no function in type"
      | Bind ((Forall | Exists),_,_) -> fail t "no quantifier in type"
      | Let (_,_,_) -> fail t "no let in type"
      | TyBuiltin b ->
          begin match b with
          | NunBuiltin.Ty.Prop -> FOI.TyBuiltin FOI.TyBuiltin.Prop
          | NunBuiltin.Ty.Kind -> fail t "kind belongs to HO fragment"
          | NunBuiltin.Ty.Type -> fail t "type belongs to HO fragment"
          end
      | TyArrow (_,_) -> fail t "arrow is not an atomic type"
      | TyMeta _ -> assert false

    let rec flatten_arrow t = match T.view t with
      | TyArrow (a, b) ->
          let l, ret = flatten_arrow b in
          a :: l, ret
      | _ -> [], t
  end

  module T = struct
    module T = Term
    type t = T.t

    let view t = match T.view t with
      | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) -> FOI.Ite (a,b,c)
      | AppBuiltin _ -> fail t "no builtin in terms"
      | Const id -> FOI.App (id, [])
      | Var v -> FOI.Var v
      | App (f,l) ->
          begin match T.view f with
          | Const id -> FOI.App (id, l)
          | _ -> fail t "application of non-constant term"
          end
      | Bind (Fun,v,t) -> FOI.Fun (v, t)
      | Bind ((Forall | Exists), _,_) -> fail t "no quantifiers in FO terms"
      | Let (v,t,u) -> FOI.Let (v, t, u)
      | TyBuiltin _
      | TyArrow (_,_)
      | Bind (TyForall, _,_) -> fail t "no types in FO terms"
      | TyMeta _ -> assert false
  end

  module Formula = struct
    module T = Term (* avoid shadowing from [T] above *)
    type t = T.t

    let view t = match T.view t with
      | AppBuiltin (b,l) ->
          begin match b, l with
          | NunBuiltin.T.True, [] -> FOI.True
          | NunBuiltin.T.False, [] -> FOI.False
          | NunBuiltin.T.Not, [f] -> FOI.Not f
          | NunBuiltin.T.Or, l -> FOI.Or l
          | NunBuiltin.T.And, l -> FOI.And l
          | NunBuiltin.T.Imply, [a;b] -> FOI.Imply (a,b)
          | NunBuiltin.T.Ite, [a;b;c] -> FOI.F_ite (a,b,c)
          | NunBuiltin.T.Equiv, [a;b] -> FOI.Equiv (a,b)
          | NunBuiltin.T.Eq, [a;b] -> FOI.Eq (a,b)
          | _ -> assert false
          end
      | App _
      | Const _ -> FOI.Atom t
      | Var _ -> fail t "no variable in FO formulas"
      | Bind (Fun,v,t) -> FOI.F_fun (v,t)
      | Bind (Forall, v,f) -> FOI.Forall (v,f)
      | Bind (Exists, v,f) -> FOI.Exists (v,f)
      | Let (_,_,_) -> FOI.Atom t
      | TyArrow (_,_)
      | Bind (TyForall, _,_)
      | TyBuiltin _ -> fail t "no types in FO formulas"
      | TyMeta _ -> assert false
  end

  type formula = Formula.t
  type term_or_form = (T.t, formula) NunFO.term_or_form_view

  let convert_statement st =
    let module St = NunProblem.Statement in
    match St.view st with
    | St.Decl (id, k, ty) ->
        begin match k with
        | St.Decl_type ->
            let args, _ = Ty.flatten_arrow ty in
            let n = List.length args in
            [ FOI.TyDecl (id, n) ]
        | St.Decl_fun ->
            let ty = Ty.flatten_arrow ty in
            [ FOI.Decl (id, ty) ]
        | St.Decl_prop ->
            let ty = Ty.flatten_arrow ty in
            [ FOI.Decl (id, ty) ]
        end
    | St.Axiom a ->
        let mk_ax x = FOI.Axiom x in
        begin match a with
        | St.Axiom_std l ->
            List.map mk_ax l
        | St.Axiom_spec s
        | St.Axiom_rec s ->
            CCList.flat_map
              (fun c ->
                (* evaluate axioms by replacing the alias by the defined term *)
                let subst = Subst.add ~subst:Subst.empty
                  c.St.case_alias c.St.case_defined in
                List.map
                  (fun ax -> mk_ax (SubstUtil.eval ~subst ax))
                  (St.case_axioms c)
              )
              s
        end
    | St.Goal f ->
        [ FOI.Goal f ]
    | St.TyDef (k, l) ->
        let n = ref 0 in
        let convert_cstor ty_id c =
          (* for now, generate dummy selectors *)
          {FOI.
            cstor_name=c.St.cstor_name;
            cstor_args=List.map
              (fun a ->
                let selector = ID.make
                  ~name:(Printf.sprintf "_select_%s_%d" (ID.name ty_id) !n)
                in
                incr n;
                selector, a
              )
              c.St.cstor_args;
          }
        in
        (* gather all variables *)
        let ty_vars =
          CCList.flat_map (fun tydef -> List.map Var.id tydef.St.ty_vars) l
        (* convert declarations *)
        and ty_types = List.map
          (fun tydef ->
            let id = tydef.St.ty_id in
            let cstors = List.map (convert_cstor id) tydef.St.ty_cstors in
            n := 0;
            id, cstors
          ) l
        in
        let l = {FOI.  ty_vars; ty_types; } in
        [ FOI.MutualTypes (k, l) ]

  let convert_problem p =
    let res = CCVector.create() in
    CCVector.iter
      (fun st ->
        let l = convert_statement st in
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

  and convert_term t = match FO.T.view t with
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
    | NunFO.F_ite (a,b,c) ->
        T.ite (convert_formula a) (convert_formula b) (convert_formula c)
    | NunFO.F_fun (v,t) ->
        let v = Var.update_ty v ~f:convert_ty in
        T.fun_ v (convert_formula t)

  let convert_t_or_f = function
    | NunFO.Term t -> convert_term t
    | NunFO.Form f -> convert_formula f

  let convert_model m = NunProblem.Model.map ~f:convert_t_or_f m
end

let to_fo (type a)(type b)(type c)
(module T : S with type t = a)
(module FO : NunFO.S with type T.t = b and type formula = c) =
  let module Sol = NunSolver_intf in
  let module Conv = AsFO(T) in
  let module ConvBack = OfFO(T)(FO) in
  NunTransform.make1
  ~name:"to_fo"
  ~encode:(fun (pb:(T.t, T.ty) NunProblem.t) ->
    let pb' = Conv.convert_problem pb in
    pb', ()
  )
  ~decode:(fun _st m ->
    ConvBack.convert_model m
  )
  ()

let to_fo_no_model (type a) (module T : S with type t = a) =
  let module Conv = AsFO(T) in
  NunTransform.make1
  ~name:"to_fo"
  ~encode:(fun (pb:(T.t, T.ty) NunProblem.t) ->
    let pb' = Conv.convert_problem pb in
    pb', ()
  )
  ~decode:(fun _ x -> x)
  ()

(** {2 Conversion} *)

module Convert(T1 : VIEW)(T2 : S) = struct
  let rec convert t = match T1.view t with
    | AppBuiltin (b,l) -> T2.app_builtin b (List.map convert l)
    | Const id -> T2.const id
    | Var v -> T2.var (aux_var v)
    | App (f,l) -> T2.app (convert f) (List.map convert l)
    | Bind (b,v,t) -> T2.mk_bind b (aux_var v) (convert t)
    | Let (v,t,u) -> T2.let_ (aux_var v) (convert t) (convert u)
    | TyBuiltin b -> T2.ty_builtin b
    | TyArrow (a,b) -> T2.ty_arrow (convert a)(convert b)
    | TyMeta _ -> assert false

  and aux_var v = Var.update_ty ~f:convert v
end

(** {2 Conversion of UntypedAST to HO, without Type-Checking} *)

module OfUntyped(T : S) = struct
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
