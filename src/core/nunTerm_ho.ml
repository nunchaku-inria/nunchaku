
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Higher-Order Terms}

  To be used after type inference, i.e. converted from {!NunTerm_typed}
*)

module ID = NunID
module Var = NunVar
module TyI = NunType_intf

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

type ('a, 'ty) view =
  | Builtin of NunBuiltin.T.t (** built-in symbol *)
  | Const of id (** top-level symbol *)
  | Var of 'ty var (** bound variable *)
  | App of 'a * 'a list
  | Fun of 'ty var * 'a
  | Forall of 'ty var * 'a
  | Exists of 'ty var * 'a
  | Let of 'ty var * 'a * 'a
  | TyKind
  | TyType
  | TyBuiltin of NunBuiltin.Ty.t (** Builtin type *)
  | TyArrow of 'ty * 'ty   (** Arrow type *)
  | TyForall of 'ty var * 'ty  (** Polymorphic/dependent type *)

module type VIEW = sig
  type t
  type ty = t

  val view : t -> (t, ty) view
end

module type S = sig
  include VIEW

  module Ty : sig
    include NunType_intf.AS_TERM with type term = t and type t = ty

    exception Error of string * t * t list
    (** Raised when a type application fails *)

    val apply : t -> t list -> t
    (** [apply t l] computes the type of [f args] where [f : t] and [args : l]
        @raise Error if the arguments do not match *)
  end

  val const : id -> t
  val builtin : NunBuiltin.T.t -> t
  val var : Ty.t var -> t
  val app : t -> t list -> t
  val fun_ : ty var -> t -> t
  val let_ : ty var -> t -> t -> t
  val forall : ty var -> t -> t
  val exists : ty var -> t -> t

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
    view: (t, t) view;
  }

  type ty = t

  (* special constants: kind and type *)
  let kind_ = {view=TyKind}
  let type_ = {view=TyType}
  let prop = {view=TyBuiltin NunBuiltin.Ty.Prop}

  let view t = t.view

  let make_raw_ view = { view}

  let make_ view = match view with
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  let builtin s = make_ (Builtin s)
  let const id = make_ (Const id)
  let var v = make_ (Var v)
  let app t l =
    if l=[] then t else make_ (App (t, l))
  let fun_ v t = make_ (Fun (v, t))
  let let_ v t u = make_ (Let (v, t, u))
  let forall v t = make_ (Forall (v, t))
  let exists v t = make_ (Exists (v, t))

  let ty_type = type_
  let ty_kind = kind_
  let ty_prop = prop

  let ty_builtin b = make_ (TyBuiltin b)
  let ty_const id = const id
  let ty_var v = var v
  let ty_app f l =
    if l=[] then f else app f l
  let ty_arrow a b = make_ (TyArrow (a,b))
  let ty_forall a b = make_ (TyForall(a,b))

  module Ty = struct
    type term = t
    type t = ty

    let view t = match t.view with
      | TyKind -> TyI.Kind
      | TyType -> TyI.Type
      | TyBuiltin b -> TyI.Builtin b
      | Const id -> TyI.Const id
      | Var v -> TyI.Var v
      | App (f,l) -> TyI.App (f,l)
      | TyArrow (a,b) -> TyI.Arrow (a,b)
      | TyForall (v,t) -> TyI.Forall (v,t)
      | Builtin _
      | Fun _
      | Forall _
      | Exists _
      | Let _ -> assert false

    let is_Type t = match t.view with
      | TyType -> true
      | _ -> false

    let is_Kind t = match t.view with
      | TyKind -> true
      | _ -> false

    let rec returns t = match t.view with
      | TyArrow (_, t')
      | TyForall (_, t') -> returns t'
      | _ -> t

    let returns_Type t = match (returns t).view with
      | TyType -> true
      | _ -> false

    module Subst = struct
      module M = Map.Make(struct
        type t = ty Var.t
        let compare = Var.compare
      end)

      type _t = ty M.t

      let empty = M.empty

      let is_empty = M.is_empty

      let find = M.find

      let bind = M.add

      let rec equal ~subst ty1 ty2 = match view ty1, view ty2 with
        | TyI.Kind, TyI.Kind
        | TyI.Type, TyI.Type -> true
        | TyI.Const id1, TyI.Const id2 -> ID.equal id1 id2
        | TyI.Var v1, _ when M.mem v1 subst ->
            equal ~subst (M.find v1 subst) ty2
        | _, TyI.Var v2 when M.mem v2 subst ->
            equal ~subst ty1 (M.find v2 subst)
        | TyI.Var v1, TyI.Var v2 -> Var.equal v1 v2
        | TyI.Builtin b1, TyI.Builtin b2 -> NunBuiltin.Ty.equal b1 b2
        | TyI.Meta v1, TyI.Meta v2 -> NunMetaVar.equal v1 v2
        | TyI.App (f1,l1), TyI.App (f2, l2) ->
            equal ~subst f1 f2
              && List.length l1 = List.length l2
              && List.for_all2 (equal ~subst) l1 l2
        | TyI.Arrow (a1,b1), TyI.Arrow (a2,b2) ->
            equal ~subst a1 a2 && equal ~subst b1 b2
        | TyI.Forall (v1, t1), TyI.Forall (v2, t2) ->
            let v = Var.fresh_copy v1 in
            let subst = bind v1 (ty_var v) (bind v2 (ty_var v) subst) in
            equal ~subst t1 t2
        | TyI.Kind ,_
        | TyI.Var _, _
        | TyI.Type ,_
        | TyI.Builtin _,_
        | TyI.Const _,_
        | TyI.Meta _,_
        | TyI.App (_,_),_
        | TyI.Arrow (_,_),_
        | TyI.Forall (_,_),_ -> false

      let rec eval ~subst ty = match view ty with
        | TyI.Kind
        | TyI.Type
        | TyI.Meta _
        | TyI.Const _
        | TyI.Builtin _ -> ty
        | TyI.Var v ->
            begin try M.find v subst
            with Not_found -> ty
            end
        | TyI.App (f,l) ->
            ty_app (eval ~subst f) (List.map (eval ~subst) l)
        | TyI.Arrow (a,b) ->
            ty_arrow (eval ~subst a) (eval ~subst b)
        | TyI.Forall (v,t) ->
            let v' = Var.fresh_copy v in
            let subst = M.add v (ty_var v') subst in
            ty_forall v' (eval ~subst t)
    end

    include TyI.Print(struct type t = ty let view = view end)

    exception Error of string * t * t list
    (** Raised when a type application fails *)

    let () = Printexc.register_printer
      (function
        | Error (msg, t, l) ->
            let msg = CCFormat.sprintf
              "@[<hv2>type error@ when applying %a@ on @[%a@]: %s@]"
                print_in_app t (CCFormat.list print_in_app) l msg
            in Some msg
        | _ -> None
      )

    let error_ msg ~hd ~l = raise (Error (msg, hd, l))

    let apply t l =
      let rec app_ ~subst t l = match view t, l with
        | _, [] ->
            if Subst.is_empty subst then t else Subst.eval ~subst t
        | TyI.Kind, _
        | TyI.Type, _
        | TyI.Builtin _, _
        | TyI.App (_,_),_
        | TyI.Const _, _ ->
            error_ "cannot apply this type" ~hd:t ~l
        | TyI.Var v, _ ->
            begin try
              let t = Subst.find v subst in
              app_ ~subst t l
            with Not_found ->
              error_ "cannot apply this type" ~hd:t ~l
            end
        | TyI.Meta _,_ -> assert false
        | TyI.Arrow (a, t'), b :: l' ->
            if Subst.equal ~subst a b
            then app_ ~subst t' l'
            else error_ "type mismatch on first argument" ~hd:t ~l
        | TyI.Forall (v,t'), b :: l' ->
            let subst = Subst.bind v b subst in
            app_ ~subst t' l'

      in
      app_ ~subst:Subst.empty t l

    include TyI.Print(struct
      type _t = t
      type t = _t
      let view = view
    end)
  end
end

(** {2 Compute Types} *)

exception Undefined of id

module ComputeType(T : S) = struct
  type signature = T.ty NunProblem.Signature.t

  let compute_signature ?(init=ID.Map.empty) =
    let module M = ID.Map in
    let module St = NunProblem.Statement in
    Sequence.fold
      (fun sigma st -> match St.view st with
        | St.Decl (id,ty) -> M.add id ty sigma
        | St.Axiom _ -> sigma
        | St.Def (id,ty,_) -> M.add id ty sigma
      ) init

  exception Undefined of id

  let () = Printexc.register_printer
    (function
      | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
      | _ -> None
    )

  let ty_of_eq =
    let v = Var.make ~ty:T.ty_type ~name:"a" in
    T.ty_forall v (T.ty_arrow (T.ty_var v) (T.ty_arrow (T.ty_var v) T.ty_prop))

  let rec ty_exn ~sigma t = match T.view t with
    | TyKind -> failwith "Term_ho.ty: kind has no type"
    | TyType -> T.ty_kind
    | Const id ->
        begin try NunID.Map.find id sigma
        with Not_found -> raise (Undefined id)
        end
    | Builtin b ->
        let module B = NunBuiltin.T in
        let prop1 = T.ty_arrow T.ty_prop T.ty_prop in
        let prop2 = T.ty_arrow T.ty_prop (T.ty_arrow T.ty_prop T.ty_prop) in
        begin match b with
          | B.Eq -> ty_of_eq
          | B.Imply -> prop2
          | B.Equiv -> prop2
          | B.Or -> prop2
          | B.And -> prop2
          | B.Not -> prop1
          | B.True -> T.ty_prop
          | B.False -> T.ty_prop
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        T.Ty.apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Fun (v,t) ->
        if T.Ty.returns_Type (Var.ty v)
        then T.ty_forall v (ty_exn ~sigma t)
        else T.ty_arrow (Var.ty v) (ty_exn ~sigma t)
    | Forall (v,_)
    | Exists (v,_) -> T.ty_arrow (Var.ty v) T.ty_prop
    | Let (_,_,u) -> ty_exn ~sigma u
    | TyBuiltin _
    | TyArrow (_,_)
    | TyForall (_,_) -> T.ty_type

  let ty ~sigma t =
    try CCError.return (ty_exn ~sigma t)
    with e -> NunUtils.err_of_exn e
end

(** {2 Printing} *)

module type PRINT = sig
  type term
  type ty

  val print : term printer
  val print_in_app : term printer
  val print_in_binder : term printer

  val print_ty : ty printer
end

module Print(T : VIEW) = struct
  type term = T.t
  type ty = T.ty

  let fpf = Format.fprintf

  let rec print out ty = match T.view ty with
    | TyKind -> CCFormat.string out "kind"
    | TyType -> CCFormat.string out "type"
    | Builtin b -> CCFormat.string out (NunBuiltin.T.to_string b)
    | TyBuiltin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Const id -> ID.print out id
    | Var v -> Var.print out v
    | App (f, [a;b]) ->
        begin match T.view f with
        | Builtin s when NunBuiltin.T.fixity s = `Infix ->
            fpf out "@[<hov>%a@ %s@ %a@]"
              print_in_app a (NunBuiltin.T.to_string s) print_in_app b
        | _ ->
            fpf out "@[<hov2>%a@ %a@ %a@]" print_in_app f
              print_in_app a print_in_app b
        end
    | App (f,l) ->
        fpf out "@[<2>%a@ %a@]" print_in_app f
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " print_in_app) l
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print v print t print u
    | Fun (v, t) ->
        fpf out "@[<2>fun %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | Forall (v, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | Exists (v, t) ->
        fpf out "@[<2>forall %a:%a.@ %a@]" Var.print v print_ty_in_app (Var.ty v) print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_ty_in_arrow a print_ty b
    | TyForall (v,t) ->
        fpf out "@[<2>forall %a:type.@ %a@]" Var.print v print_ty t

  and print_ty out ty = print out (ty:T.ty:>T.t)
  and print_ty_in_app out ty = print_in_app out (ty:T.ty:>T.t)
  and print_ty_in_arrow out ty = print_in_binder out (ty:T.ty:>T.t)

  and print_in_app out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType | Var _ | Const _ ->
        print out t
    | App (_,_)
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t

  and print_in_binder out t = match T.view t with
    | Builtin _ | TyBuiltin _ | TyKind | TyType | Var _ | Const _ | App (_,_) ->
        print out t
    | Forall _
    | Exists _
    | Fun _
    | Let _
    | TyArrow (_,_)
    | TyForall (_,_) -> fpf out "@[(%a)@]" print t
end

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
    | Builtin b ->
        let b = match b with
          | NunBuiltin.T.True  -> Untyped.Builtin.True
          | NunBuiltin.T.False -> Untyped.Builtin.False
          | NunBuiltin.T.Not -> Untyped.Builtin.Not
          | NunBuiltin.T.Or -> Untyped.Builtin.Or
          | NunBuiltin.T.And -> Untyped.Builtin.And
          | NunBuiltin.T.Imply -> Untyped.Builtin.Imply
          | NunBuiltin.T.Equiv -> Untyped.Builtin.Equiv
          | NunBuiltin.T.Eq -> Untyped.Builtin.Eq
        in Untyped.builtin b
    | Const id -> Untyped.var (find_ ~ctx id)
    | Var v -> Untyped.var (find_ ~ctx (Var.id v))
    | App (f,l) -> Untyped.app (erase ~ctx f) (List.map (erase ~ctx) l)
    | Fun (v,t) ->
        enter_typed_var_ ~ctx v (fun v' -> Untyped.fun_ v' (erase ~ctx t))
    | Forall (v,t) ->
        enter_typed_var_ ~ctx v (fun v' -> Untyped.forall v' (erase ~ctx t))
    | Exists (v,t) ->
        enter_typed_var_ ~ctx v (fun v' -> Untyped.forall v' (erase ~ctx t))
    | Let (v,t,u) ->
        let t = erase ~ctx t in
        enter_ ~ctx v
          (fun v' ->
            Untyped.let_ v' t (erase ~ctx u)
          )
    | TyKind -> failwith "HO.erase: cannot erase Kind"
    | TyType -> Untyped.builtin Untyped.Builtin.Type
    | TyBuiltin b ->
        let b = match b with
          | NunBuiltin.Ty.Prop -> Untyped.Builtin.Prop
        in
        Untyped.builtin b
    | TyArrow (a,b) -> Untyped.ty_arrow (erase_ty ~ctx a) (erase_ty ~ctx b)
    | TyForall (v,t) ->
        enter_ ~ctx v (fun v' -> Untyped.ty_forall v' (erase_ty ~ctx t))

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

module AsFO(T : VIEW) = struct
  exception NotInFO of string * T.t

  let () = Printexc.register_printer
    (function
      | NotInFO (msg, t) ->
          let module P = Print(T) in
          let msg = CCFormat.sprintf
            "@[term @[%a@] is not in the first-order fragment:@ %s@]"
            P.print_in_app t msg
          in
          Some msg
      | _ -> None
    )

  module FOI = NunFO

  let fail t msg = raise (NotInFO (msg, t))

  module Ty = struct
    type t = T.t
    type toplevel_ty = t list * t

    let view t = match T.view t with
      | Builtin _ -> fail t "builtin term"
      | Const id -> FOI.TyApp (id, [])
      | Var _ -> fail t "variable in type"
      | App (f,l) ->
          begin match T.view f with
          | Const id -> FOI.TyApp (id, l)
          | _ -> fail t "non-constant application"
          end
      | Fun (_,_) -> fail t "no function in type"
      | Forall (_,_)
      | Exists (_,_) -> fail t "no quantifier in type"
      | Let (_,_,_) -> fail t "no let in type"
      | TyKind -> fail t "kind belongs to HO fragment"
      | TyType -> fail t "type belongs to HO fragment"
      | TyBuiltin b ->
          begin match b with
          | NunBuiltin.Ty.Prop -> FOI.TyBuiltin FOI.TyBuiltin.Prop
          end
      | TyArrow (_,_) -> fail t "arrow is not an atomic type"
      | TyForall (_,_) -> fail t "no quantification in FO types"

    let rec flatten_arrow t = match T.view t with
      | TyArrow (a, b) ->
          let l, ret = flatten_arrow b in
          a :: l, ret
      | _ ->
          ignore (view t); (* check atomicity quickly *)
          [], t
  end

  module T = struct
    type t = T.t

    let view t = match T.view t with
      | Builtin _ -> fail t "no builtin in terms"
      | Const _
      | Var _
      | App (_,_)
      | Fun (_,_)
      | Forall (_,_)
      | Exists (_,_)
      | Let (_,_,_)
      | TyKind
      | TyType
      | TyBuiltin _
      | TyArrow (_,_)
      | TyForall (_,_) -> assert false
  end

  module Formula = struct
    type t = T.t

    let view t = match T.view t with
      | Builtin b ->
          begin match b with
          | NunBuiltin.T.True -> FOI.True
          | NunBuiltin.T.False -> FOI.False
          | NunBuiltin.T.Not
          | NunBuiltin.T.Or
          | NunBuiltin.T.And
          | NunBuiltin.T.Imply
          | NunBuiltin.T.Equiv
          | NunBuiltin.T.Eq  -> fail t "connective not fully applied"
          end
      | Const _ -> FOI.Atom t
      | Var _ -> fail t "no variable in FO formulas"
      | App (_, []) -> assert false
      | App (f,l) ->
          begin match T.view f, l with
          | Builtin NunBuiltin.T.Not, [f] -> FOI.Not f
          | Builtin NunBuiltin.T.And, _ -> FOI.And l
          | Builtin NunBuiltin.T.Or, _ -> FOI.Or l
          | Builtin NunBuiltin.T.Imply, [a;b] -> FOI.Imply (a,b)
          | Builtin NunBuiltin.T.Equiv, [a;b] -> FOI.Equiv (a,b)
          | Builtin NunBuiltin.T.Eq, [a;b] -> FOI.Eq (a,b)
          | Builtin _, _ -> fail t "wrong builtin/arity"
          | Const _, _ -> FOI.Atom t
          | _ -> fail t "wrong application in FO formula"
          end
      | Fun (_,_) -> fail t "function in FO"
      | Forall (v,f) -> FOI.Forall (v,f)
      | Exists (v,f) -> FOI.Exists (v,f)
      | Let (_,_,_) -> FOI.Atom t
      | TyArrow (_,_)
      | TyForall (_,_)
      | TyKind
      | TyBuiltin _
      | TyType -> fail t "no types in FO formulas"
  end

  let convert_statement st =
    let module St = NunProblem.Statement in
    match St.view st with
    | St.Decl (id,ty) ->
        let ty = Ty.flatten_arrow ty in
        FOI.Decl (id, ty)
    | St.Def (id,ty,t) ->
        let ty = Ty.flatten_arrow ty in
        FOI.Def (id, ty, t)
    | St.Axiom f -> FOI.Axiom f

  let convert_problem p =
    NunProblem.statements p
    |> CCList.map convert_statement
    |> FOI.Problem.make
end

let as_fo (type a) (module T : VIEW with type t = a) =
  let module U = AsFO(T) in
  (module U : NunFO.VIEW with type T.t = a and type Ty.t = a and type Formula.t = a)

