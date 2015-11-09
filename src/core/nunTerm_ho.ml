
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

type ('t, 'inv) repr = ('t, 'inv) NunTerm_intf.repr
type ('t, 'inv) build = ('t, 'inv) NunTerm_intf.build

module type REPR = sig
  type 'inv t
  val repr : ('inv t,'inv) repr
end

module type BUILD = sig
  type 'inv t
  val build : ('inv t,'inv) build
end

module type S = sig
  type 'inv t
  include REPR with type 'a t := 'a t
  include BUILD with type 'a t := 'a t
end

module Default : S = struct
  type 'inv t = {
    view: ('inv t, 'inv) view;
  }

  let repr t = t.view

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
    | App ({view=AppBuiltin (b, l1); _}, l2) ->
        make_raw_ (AppBuiltin (b, l1 @ l2))
    | _ -> make_raw_ view
end

(** {2 Packed Term} *)

type packed = Packed : 't * ('t, _) repr -> packed

let pack ~repr t = Packed (t, repr)

(** {2 Utils} *)

let app_builtin ~build s l = build (AppBuiltin (s,l))
let builtin ~build s = app_builtin ~build s []
let const ~build id = build (Const id)
let var ~build v = build (Var v)
let app ~build t l = build (App(t,l))
let mk_bind ~build b v t = build (Bind (b,v,t))
let fun_ ~build v t = build (Bind (Fun,v, t))
let let_ ~build v t u = build (Let (v, t, u))
let match_with ~build t l =
  if ID.Map.is_empty l then invalid_arg "Term_ho.case: empty list of cases";
  build (Match (t,l))
let ite ~build a b c =
  app ~build (builtin ~build NunBuiltin.T.Ite) [a;b;c]
let forall ~build v t = build (Bind(Forall,v, t))
let exists ~build v t = build (Bind(Exists,v, t))
let eq ~build a b = app ~build (builtin ~build NunBuiltin.T.Eq) [a;b]

let ty_type ~build = build (TyBuiltin NunBuiltin.Ty.Type)
let ty_kind ~build = build (TyBuiltin NunBuiltin.Ty.Kind)
let ty_prop ~build = build (TyBuiltin NunBuiltin.Ty.Prop)

let ty_builtin ~build b = build (TyBuiltin b)
let ty_const ~build id = const ~build id
let ty_app ~build f l = if l=[] then f else app ~build f l
let ty_arrow ~build a b = build (TyArrow (a,b))
let ty_forall ~build v t = build (Bind (TyForall,v,t))
let ty_var ~build v = build (TyVar v)

let as_ty
: type t inv.  repr:(t,inv) repr -> (t,inv) TyI.repr
= fun ~repr t -> match repr t with
  | TyBuiltin b -> TyI.Builtin b
  | Const id -> TyI.Const id
  | App (f,l) -> TyI.App (f,l)
  | TyArrow (a,b) -> TyI.Arrow (a,b)
  | TyVar v -> TyI.Var v
  | Bind (TyForall, v, t) -> TyI.Forall (v,t)
  | TyMeta v -> TyI.Meta v
  | AppBuiltin _
  | Match _
  | Var _
  | Let _ -> assert false
  | Bind _ -> assert false

(*$T
  Default.Ty.returns_Type Default.ty_type
  Default.Ty.returns_Type Default.(ty_arrow ty_prop ty_type)
  not (Default.Ty.returns_Type Default.(ty_arrow ty_type ty_prop))
*)

module Util(T : S) = struct
  let build = T.build

  let ty_type () = build (TyBuiltin NunBuiltin.Ty.Type)
  let ty_kind () = build (TyBuiltin NunBuiltin.Ty.Kind)
  let ty_prop () = build (TyBuiltin NunBuiltin.Ty.Prop)

  let app_builtin s l = build (AppBuiltin (s,l))
  let builtin s = app_builtin s []
  let const id = build (Const id)
  let var v = build (Var v)
  let app t l = build (App(t,l))
  let mk_bind b v t = build (Bind (b,v,t))
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

  let ty_builtin b = build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l = if l=[] then f else app f l
  let ty_arrow a b = build (TyArrow (a,b))
  let ty_forall v t = build (Bind (TyForall,v,t))
  let ty_var v = build (TyVar v)

  let as_ty t = as_ty ~repr:T.repr t
  let pack t = pack ~repr:T.repr t
end

(** {2 Printing} *)

type 't print_funs = {
  print : 't printer;
  print_in_app : 't printer;
  print_in_binder : 't printer;
  print_ty : 't printer;
}

let fpf = Format.fprintf
let pp_list_ ?(start="") ?(stop="") ~sep pp =
  CCFormat.list ~start ~stop ~sep pp

let mk_print
: type t inv. repr:(t,inv) repr -> t print_funs
= fun ~repr ->
  let rec print out t = match repr t with
    | TyBuiltin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
    | Const id -> ID.print_no_id out id
    | TyMeta v -> NunMetaVar.print out v
    | TyVar v -> Var.print out v
    | Var v -> Var.print out v
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        fpf out "@[<2>if %a@ then %a@ else %a@]"
          print a print b print c
    | AppBuiltin (NunBuiltin.T.DataTest c, [t]) ->
        fpf out "@[<2>is-%a@ %a@]" ID.print_name c print_in_app t
    | AppBuiltin (NunBuiltin.T.DataSelect (c,n), [t]) ->
        fpf out "@[<2>select-%a-%d@ %a@]" ID.print_name c n print_in_app t
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
  and print_in_app out t = match repr t with
    | AppBuiltin (_,[]) | TyBuiltin _ | Const _ -> print out t
    | TyMeta _ -> print out t
    | Var _ -> print out t
    | TyVar _ -> print out t
    | App (_,_) | AppBuiltin (_,_::_)
    | Let _ | Match _ -> fpf out "(@[%a@])" print t
    | Bind _ -> fpf out "(@[%a@])" print t
    | TyArrow (_,_) -> fpf out "(@[%a@])" print t
  and print_in_binder out t = match repr t with
    | TyBuiltin _ | Const _ | App (_,_) | AppBuiltin _ ->
        print out t
    | Var _ -> print out t
    | TyVar _ -> print out t
    | TyMeta _ -> print out t
    | Bind _ -> fpf out "(@[%a@])" print t
    | Let _ | Match _ | TyArrow (_,_) -> fpf out "(@[%a@])" print t
  in
  { print; print_in_app; print_in_binder; print_ty; }

let print ~repr = (mk_print ~repr).print
let print_ty ~repr = (mk_print ~repr).print_ty
let print_in_app ~repr = (mk_print ~repr).print_in_app
let print_in_binder ~repr = (mk_print ~repr).print_in_binder

(** {2 Utils with Substitutions} *)

exception Undefined of id

let () = Printexc.register_printer
  (function
    | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
    | _ -> None
  )

module SubstUtil(T : S) = struct
  module Subst = Var.Subst
  module U = Util(T)

  type 'i subst = ('i T.t, 'i T.t) Subst.t

  let rec equal
  : type inv. subst:inv subst -> inv T.t -> inv T.t -> bool
  = fun ~subst ty1 ty2 ->
    match T.repr ty1, T.repr ty2 with
    | Const id1, Const id2 -> ID.equal id1 id2
    | Var v1, _ when Subst.mem ~subst v1 ->
        equal ~subst (Subst.find_exn ~subst v1) ty2
    | _, Var v2 when Subst.mem ~subst v2 ->
        equal ~subst ty1 (Subst.find_exn ~subst v2)
    | TyVar v1, TyVar v2 -> Var.equal v1 v2
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
          let subst = Subst.add ~subst v1 (U.var v) in
          let subst = Subst.add ~subst v2 (U.var v) in
          equal ~subst t1 t2)
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
                let subst = Subst.add ~subst v1 (U.var v) in
                let subst = Subst.add ~subst v2 (U.var v) in
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
    | Let (_,_,_),_
    | TyArrow (_,_),_ -> false
    | Bind _, _ -> false
    | TyMeta _,_ -> false
    | TyVar _, _ -> false

  let rec deref ~subst t = match T.repr t with
    | Var v ->
        begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
        end
    | _ -> t

  (* NOTE: when dependent types are added, substitution in types is needed *)

  let rec eval
  : type inv. subst:inv subst -> inv T.t -> inv T.t
  = fun ~subst t -> match T.repr t with
    | TyMeta _ -> t
    | Const _
    | TyBuiltin _ -> t
    | AppBuiltin (_,[]) -> t
    | AppBuiltin (b,l) ->
        U.app_builtin b (List.map (eval ~subst) l)
    | Bind (b, v, t) ->
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (U.var v') in
        U.mk_bind b v' (eval ~subst t)
    | Let (v,t,u) ->
        let v' = Var.fresh_copy v in
        let t = eval ~subst t in
        let subst = Subst.add ~subst v (U.var v') in
        U.let_ v' t (eval ~subst u)
    | Match (t,l) ->
        let t = eval ~subst t in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let vars' = Var.fresh_copies vars in
            let subst = Subst.add_list ~subst vars (List.map U.var vars') in
            vars', eval ~subst rhs
          ) l
        in
        U.match_with t l
    | Var v -> CCOpt.get t (Subst.find ~subst v)
    | TyVar v -> CCOpt.get t (Subst.find ~subst v)
    | App (f,l) ->
        U.app (eval ~subst f) (List.map (eval ~subst) l)
    | TyArrow (a,b) ->
        U.ty_arrow (eval ~subst a) (eval ~subst b)

  exception ApplyError of string * packed * packed list
  (** Raised when a type application fails *)

  exception UnifError of string * packed * packed
  (** Raised for unification or matching errors *)

  let () =
    let pp_packed out (Packed (t,repr)) = print_in_app ~repr out t in
    Printexc.register_printer
    (function
      | ApplyError (msg, t, l) ->
          let msg = CCFormat.sprintf
            "@[<hv2>type error@ when applying %a@ on @[%a@]: %s@]"
              pp_packed t (CCFormat.list pp_packed) l msg
          in Some msg
      | UnifError (msg, t1, t2) ->
          let msg = CCFormat.sprintf
            "@[<hv2>unification error@ for %a@ and@ %a: %s@]"
              pp_packed t1 pp_packed t2 msg
          in Some msg
      | _ -> None
    )

  let error_apply_ msg ~hd ~l = raise (ApplyError (msg, U.pack hd, List.map U.pack l))
  let error_unif_ msg t1 t2 = raise (UnifError (msg, U.pack t1, U.pack t2))

  let ty_apply_full
  : type inv. inv T.t -> inv T.t list -> inv T.t * inv subst
  = fun t l ->
    let rec app_
    : type inv. subst:inv subst -> inv T.t -> inv T.t list -> inv T.t * inv subst
    = fun ~subst t l -> match U.as_ty t, l with
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
          else error_apply_
            "type mismatch on first argument" ~hd:t ~l
      | TyI.Forall (v,t'), b :: l' ->
          let subst = Subst.add ~subst v b in
          app_ ~subst t' l'
    in
    app_ ~subst:Subst.empty t l

  let ty_apply t l =
    let t, subst = ty_apply_full t l in
    if Subst.is_empty subst then t else eval ~subst t

  let rec get_ty_arg_
  : type t inv. repr:(t,inv) TyI.repr -> t -> int -> t option
  = fun ~repr ty i -> match repr ty with
    | TyI.App (_,_)
    | TyI.Builtin _
    | TyI.Const _ -> None
    | TyI.Var _ -> None
    | TyI.Meta _ -> None
    | TyI.Arrow (a,b) ->
        if i=0 then Some a else get_ty_arg_ ~repr b (i-1)
    | TyI.Forall (_,_) -> None

  type 'inv signature = id -> 'inv T.t option

  let find_ty_ ~sigma id = match sigma id with
    | Some ty -> ty
    | None -> raise (Undefined id)

  let rec ty_exn
  : type inv_m.
      sigma:(<poly:[`Poly];meta:inv_m> as 'inv) signature -> 'inv T.t -> 'inv T.t
  = fun ~sigma t -> match T.repr t with
    | Const id -> find_ty_ ~sigma id
    | AppBuiltin (b,_) ->
        let module B = NunBuiltin.T in
        let prop = U.ty_prop () in
        let prop1 = U.ty_arrow prop prop in
        let prop2 = U.ty_arrow prop (U.ty_arrow prop prop) in
        begin match b with
          | B.Equiv
          | B.Imply
          | B.Or
          | B.And -> prop2
          | B.Not -> prop1
          | B.True
          | B.False
          | B.Ite
          | B.Eq -> prop
          | B.DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = find_ty_ ~sigma id in
              U.ty_arrow (TyI.returns ~repr:U.as_ty ty) prop
          | B.DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = find_ty_ ~sigma id in
              begin match get_ty_arg_ ~repr:U.as_ty ty n with
              | None ->
                  failwith "cannot infer type, wrong argument to DataSelect"
              | Some ty_arg ->
                  U.ty_arrow (TyI.returns ~repr:U.as_ty ty) ty_arg
              end
        end
    | Var v -> Var.ty v
    | TyVar v ->
        assert (equal ~subst:Subst.empty (U.ty_type()) (Var.ty v));
        Var.ty v
    | App (f,l) ->
        ty_apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Bind (b,v,t) ->
        begin match b with
        | Forall
        | Exists -> U.ty_arrow (Var.ty v) (U.ty_prop())
        | Fun ->
            if TyI.returns_Type ~repr:U.as_ty (Var.ty v)
            then U.ty_forall v (ty_exn ~sigma t)
            else U.ty_arrow (Var.ty v) (ty_exn ~sigma t)
        | TyForall -> U.ty_type()
        end
    | Let (_,_,u) -> ty_exn ~sigma u
    | Match (_,m) ->
        let _, (_, rhs) = ID.Map.choose m in
        ty_exn ~sigma rhs
    | TyMeta _ -> assert false
    | TyBuiltin b ->
        begin match b with
        | NunBuiltin.Ty.Kind -> failwith "Term_ho.ty: kind has no type"
        | NunBuiltin.Ty.Type -> U.ty_kind()
        | NunBuiltin.Ty.Prop -> U.ty_type()
        end
    | TyArrow (_,_) -> U.ty_type()

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
      f1::l1, (U.app f2 l2_1) :: l2_2
    else
      let l1_1, l1_2 = CCList.take_drop (n1-n2) l1 in
      (U.app f1 l1_1) :: l1_2, f2 :: l2

  let match_exn
  : type inv. ?subst2:inv subst -> inv T.t -> inv T.t -> inv subst
  = fun ?(subst2=Subst.empty) t1 t2 ->
    (* bound: bound variables in t1 and t2 *)
    let rec match_
    : inv subst -> inv T.t -> inv T.t -> inv subst
    = fun subst t1 t2 ->
      let t2 = deref ~subst:subst2 t2 in
      match T.repr t1, T.repr t2 with
      | AppBuiltin (b1,l1), AppBuiltin (b2,l2)
          when NunBuiltin.T.equal b1 b2 && List.length l1 = List.length l2 ->
            List.fold_left2 match_ subst l1 l2
      | Const id1, Const id2 when ID.equal id1 id2 -> subst
      | Var v1, _ -> match_var subst v1 t1 t2
      | TyVar v1, _ -> match_var subst v1 t1 t2
      | App (f1, l1), App (f2, l2) ->
          (* right-parenthesed application *)
          let l1, l2 = unif_l_ f1 l1 f2 l2 in
          List.fold_left2 match_ subst l1 l2
      | TyArrow (a1, b1), TyArrow (a2,b2) ->
          let subst = match_ subst a1 a2 in
          match_ subst b1 b2
      | Bind _, _ -> invalid_arg "pattern is not first-order"
      | Let (_, _, _), _
      | Match _, _ -> invalid_arg "pattern is not first-order"
      | TyBuiltin b1, TyBuiltin b2 when NunBuiltin.Ty.equal b1 b2 -> subst
      | TyMeta _, _ -> assert false
      | AppBuiltin _, _
      | Const _, _
      | App (_, _), _
      | TyArrow _, _
      | TyBuiltin _, _ -> error_unif_ "do not match" t1 t2
    and match_var subst v t1 t2 =
      match Subst.find ~subst v with
      | None ->
          (* NOTE: no occur check, we assume t1 and t2 share no variables *)
          Subst.add ~subst v t2
      | Some t1' ->
          if equal ~subst t1' t2
            then subst
            else error_unif_ "incompatible variable binding" t1 t2
    in
    match_ Subst.empty t1 t2

  let match_ ?subst2 t1 t2 =
    try Some (match_exn ?subst2 t1 t2)
    with UnifError _ -> None

  (* TODO write test *)
end

(** {2 Type Erasure} *)

module Erase = struct
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

  let erase
  : type t inv. repr:(t,inv) repr -> ctx:ctx -> t -> Untyped.term
  = fun ~repr ~ctx t ->
    let rec aux t = match repr t with
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        Untyped.ite (aux a)(aux b)(aux c)
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
        Untyped.app (Untyped.builtin b) (List.map aux l)
    | Const id -> Untyped.var (find_ ~ctx id)
    | Var v -> Untyped.var (find_ ~ctx (Var.id v))
    | TyVar v -> Untyped.var (find_ ~ctx (Var.id v))
    | App (f,l) -> Untyped.app (aux f) (List.map aux l)
    | Bind (b,v,t) ->
        enter_typed_var_ ~ctx v
          (fun v' ->
            let t = aux t in
            match b with
            | Fun -> Untyped.fun_ v' t
            | Forall -> Untyped.forall v' t
            | Exists -> Untyped.exists v' t
            | TyForall -> Untyped.ty_forall (fst v') t
          )
    | Let (v,t,u) ->
        let t = aux t in
        enter_ ~ctx v
          (fun v' ->
            Untyped.let_ v' t (aux u)
          )
    | Match _ -> assert false (* TODO *)
    | TyBuiltin b ->
        let b = match b with
          | NunBuiltin.Ty.Prop -> Untyped.Builtin.Prop
          | NunBuiltin.Ty.Type -> Untyped.Builtin.Type
          | NunBuiltin.Ty.Kind -> failwith "HO.erase: cannot erase Kind"
        in
        Untyped.builtin b
    | TyArrow (a,b) -> Untyped.ty_arrow (aux a) (aux b)
    | TyMeta _ -> assert false
    (* enter a typed variable *)
    and enter_typed_var_ ~ctx v f =
      enter_ ~ctx v
        (fun v' ->
          let ty = aux (Var.ty v) in
          f (v', Some ty)
        )
    in
    aux t

  let erase_ty = erase
end

type to_fo_invariant = <poly:[`Mono]; meta:[`NoMeta]>

module ToFO(FO : NunFO.S) = struct
  exception NotInFO of string * packed

  type invariant = to_fo_invariant

  let () = Printexc.register_printer
    (function
      | NotInFO (msg, t) ->
          let pppacked out (Packed (t,repr)) = print ~repr out t in
          let msg = CCFormat.sprintf
            "@[<2>term `@[%a@]` is not in the first-order fragment:@ %s@]"
              pppacked t msg
          in
          Some msg
      | _ -> None
    )

  module FOI = NunFO
  module Subst = Var.Subst

  let fail_ t msg = raise (NotInFO (msg, t))

  let rec conv_ty
  : type t. repr:(t, invariant) repr -> t -> FO.Ty.t
  = fun ~repr t -> match repr t with
    | Var _ -> fail_ (pack ~repr t) "variable in type"
    | TyBuiltin b ->
        begin match b with
        | NunBuiltin.Ty.Prop -> FO.Ty.builtin FOI.TyBuiltin.Prop
        | NunBuiltin.Ty.Kind -> fail_ (pack ~repr t) "kind belongs to HO fragment"
        | NunBuiltin.Ty.Type -> fail_ (pack ~repr t) "type belongs to HO fragment"
        end
    | Const id -> FO.Ty.const id
    | App (f,l) ->
        begin match repr f with
        | Const id -> FO.Ty.app id (List.map (conv_ty ~repr) l)
        | _ -> fail_ (pack ~repr t) "non-constant application"
        end
    | TyArrow _ -> fail_ (pack ~repr t) "arrow in atomic type"
    | Let _
    | Match _
    | AppBuiltin _
    | Bind _ -> fail_ (pack ~repr t) "not a type"

  let conv_var ~repr = Var.update_ty ~f:(conv_ty ~repr)

  (* find arguments *)
  let rec flat_arrow_ ~repr t = match repr t with
    | TyArrow (a, b) ->
        let args, ret = flat_arrow_ ~repr b in
        a :: args, ret
    | _ -> [], t

  let conv_top_ty ~repr t =
    let args, ret = flat_arrow_ ~repr t in
    let args = List.map (conv_ty ~repr) args
    and ret = conv_ty ~repr ret in
    args, ret

  let rec conv_term ~repr t =
    let rec aux t = match repr t with
    | AppBuiltin (NunBuiltin.T.Ite, [a;b;c]) ->
        FO.T.ite (conv_form_rec ~repr a) (aux b) (aux c)
    | AppBuiltin (NunBuiltin.T.DataTest c, [t]) ->
        FO.T.data_test c (aux t)
    | AppBuiltin (NunBuiltin.T.DataSelect (c,n), [t]) ->
        FO.T.data_select c n (aux t)
    | AppBuiltin _ -> fail_ (pack ~repr t) "no builtin in terms"
    | Const id -> FO.T.const id
    | Var v -> FO.T.var (conv_var ~repr v)
    | App (f,l) ->
        begin match repr f with
        | Const id -> FO.T.app id (List.map aux l)
        | _ -> fail_ (pack ~repr t) "application of non-constant term"
        end
    | Bind (Fun,v,t) -> FO.T.fun_ (conv_var ~repr v) (aux t)
    | Bind ((Forall | Exists), _,_) -> fail_ (pack ~repr t) "no quantifiers in FO terms"
    | Let (v,t,u) ->
        FO.T.let_ (conv_var ~repr v) (aux t) (aux u)
    | Match _ -> fail_ (pack ~repr t) "no case in FO terms"
    | TyBuiltin _
    | TyArrow (_,_) -> fail_ (pack ~repr t) "no types in FO terms"
    in
    aux t

  and conv_form_rec ~repr t =
    let rec aux t = match repr t with
    | AppBuiltin (b,l) ->
        begin match b, l with
        | NunBuiltin.T.True, [] -> FO.Formula.true_
        | NunBuiltin.T.False, [] -> FO.Formula.false_
        | NunBuiltin.T.Not, [f] -> FO.Formula.not_ (aux f)
        | NunBuiltin.T.Or, l -> FO.Formula.or_ (List.map aux l)
        | NunBuiltin.T.And, l -> FO.Formula.and_ (List.map aux l)
        | NunBuiltin.T.Imply, [a;b] ->
            FO.Formula.imply (aux a) (aux b)
        | NunBuiltin.T.Ite, [a;b;c] ->
            FO.Formula.f_ite
              (aux a)(aux b) (aux c)
        | NunBuiltin.T.Equiv, [a;b] ->
            FO.Formula.equiv (aux a)(aux b)
        | NunBuiltin.T.Eq, [a;b] ->
            (* TODO: here use signature! maybe it's an equivalence *)
            FO.Formula.eq (conv_term ~repr a)(conv_term ~repr b)
        | NunBuiltin.T.DataSelect _, _
        | NunBuiltin.T.DataTest _, _ ->
            FO.Formula.atom (conv_term ~repr t)
        | _ -> assert false
        end
    | App _
    | Const _ -> FO.Formula.atom (conv_term ~repr t)
    | Var _ -> fail_ (pack ~repr t) "no variable in FO formulas"
    | Bind (Fun,v,t) ->
        FO.Formula.f_fun (conv_var ~repr v) (aux t)
    | Bind (Forall, v,f) ->
        FO.Formula.forall (conv_var ~repr v) (aux f)
    | Bind (Exists, v,f) ->
        FO.Formula.exists (conv_var ~repr v) (aux f)
    | Let (v,t,u) ->
        FO.Formula.f_let
          (conv_var ~repr v) (aux t) (aux u)
    | Match _ -> fail_ (pack ~repr t) "no match in FO formulas"
    | TyArrow (_,_)
    | TyBuiltin _ -> fail_ (pack ~repr t) "no types in FO formulas"
    in
    aux t

  let conv_form ~repr f =
    NunUtils.debugf 3
      "@[<2>convert to FO the formula `@[%a@]`@]" (fun k -> k (print ~repr) f);
    conv_form_rec ~repr f

  (* does [ty] return prop? *)
  let returns_prop_ ~repr ty =
    let ty_repr = as_ty ~repr in
    match ty_repr (TyI.returns ~repr:ty_repr ty) with
      | TyI.Builtin NunBuiltin.Ty.Prop -> true
      | _ -> false

  let convert_statement ~repr ~sigma (st:(_,_,[`Linear]) NunStatement.t) =
    let module St = NunStatement in
    match St.view st with
    | St.Decl (id, k, ty) ->
        begin match k with
        | St.Decl_type ->
            let n = TyI.num_param ~repr:(as_ty ~repr) ty in
            [ FOI.TyDecl (id, n) ]
        | St.Decl_fun ->
            let ty = conv_top_ty ~repr ty in
            [ FOI.Decl (id, ty) ]
        | St.Decl_prop ->
            let ty = conv_top_ty ~repr ty in
            [ FOI.Decl (id, ty) ]
        end
    | St.Axiom a ->
        let mk_ax x = FOI.Axiom x in
        begin match a with
        | St.Axiom_std l ->
            List.map (fun ax -> conv_form ~repr ax |> mk_ax) l
        | St.Axiom_spec s ->
            List.map
              (fun ax -> ax |> conv_form ~repr |> mk_ax)
              s.St.spec_axioms
        | St.Axiom_rec s ->
            CCList.flat_map
              (fun def ->
                let head = def.St.rec_defined.St.defined_head in
                List.map
                  (fun eqn -> match eqn with
                  | St.Eqn_linear (vars,rhs) ->
                    let vars = List.map (conv_var ~repr) vars in
                    let args = List.map FO.T.var vars in
                    let lhs = FO.T.app head args in
                    let f =
                      if returns_prop_ ~repr (Sig.find_exn ~sigma head)
                      then
                        FO.Formula.equiv
                          (FO.Formula.atom lhs)
                          (conv_form ~repr rhs)
                      else FO.Formula.eq lhs (conv_term ~repr rhs)
                    in
                    let f = List.fold_right FO.Formula.forall vars f in
                    mk_ax f
                  )
                  def.St.rec_eqns
              )
              s
        end
    | St.Goal f ->
        [ FOI.Goal (conv_form ~repr f) ]
    | St.TyDef (k, l) ->
        let convert_cstor c =
          {FOI.
            cstor_name=c.St.cstor_name;
            cstor_args=List.map (conv_ty ~repr) c.St.cstor_args;
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

  let convert_problem ~repr p =
    let res = CCVector.create() in
    let sigma = NunProblem.signature p in
    CCVector.iter
      (fun st ->
        let l = convert_statement ~repr ~sigma st in
        CCVector.append_seq res (Sequence.of_list l)
      )
      (NunProblem.statements p);
    res |> CCVector.freeze |> FOI.Problem.make
end

module OfFO(T:S)(FO : NunFO.VIEW) = struct
  module U = Util(T)
  type t = to_fo_invariant T.t

  let rec convert_ty t = match FO.Ty.view t with
    | NunFO.TyBuiltin b ->
        let b = match b with
          | NunFO.TyBuiltin.Prop -> NunBuiltin.Ty.Prop
        in U.ty_builtin b
    | NunFO.TyApp (f,l) ->
        let l = List.map convert_ty l in
        U.ty_app (U.ty_const f) l

  let rec convert_term t =
    let module B = NunBuiltin.T in
    match FO.T.view t with
    | NunFO.Builtin b ->
        let b = match b with
          | NunFO.Builtin.Int _ -> NunUtils.not_implemented "conversion from int"
        in
        U.builtin b
    | NunFO.Var v ->
        U.var (Var.update_ty v ~f:(convert_ty))
    | NunFO.App (f,l) ->
        let l = List.map convert_term l in
        U.app (U.const f) l
    | NunFO.Fun (v,t) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        U.fun_ v (convert_term t)
    | NunFO.DataTest (c,t) ->
        U.app_builtin (B.DataTest c) [convert_term t]
    | NunFO.DataSelect (c,n,t) ->
        U.app_builtin (B.DataSelect (c,n)) [convert_term t]
    | NunFO.Let (v,t,u) ->
        let v = Var.update_ty v ~f:(convert_ty) in
        U.let_ v (convert_term t) (convert_term u)
    | NunFO.Ite (a,b,c) ->
        U.ite (convert_formula a) (convert_term b) (convert_term c)

  and convert_formula f =
    let module B = NunBuiltin.T in
    match FO.Formula.view f with
    | NunFO.Atom t -> convert_term t
    | NunFO.True -> U.builtin B.True
    | NunFO.False -> U.builtin B.False
    | NunFO.Eq (a,b) -> U.eq (convert_term a) (convert_term b)
    | NunFO.And l ->
        U.app (U.builtin B.And) (List.map convert_formula l)
    | NunFO.Or l ->
        U.app (U.builtin B.Or) (List.map convert_formula l)
    | NunFO.Not f ->
        U.app (U.builtin B.Not) [convert_formula f]
    | NunFO.Imply (a,b) ->
        U.app (U.builtin B.Imply) [convert_formula a; convert_formula b]
    | NunFO.Equiv (a,b) ->
        U.eq (convert_formula a) (convert_formula b)
    | NunFO.Forall (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        U.forall v (convert_formula t)
    | NunFO.Exists (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        U.exists v (convert_formula t)
    | NunFO.F_let (v,t,u) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        U.let_ v (convert_formula t) (convert_formula u)
    | NunFO.F_ite (a,b,c) ->
        U.ite (convert_formula a) (convert_formula b) (convert_formula c)
    | NunFO.F_fun (v,t) ->
        let v = Var.update_ty v ~f:convert_formula_ty in
        U.fun_ v (convert_formula t)
  and convert_formula_ty = convert_ty

  let convert_t_or_f = function
    | NunFO.Term t -> convert_term t
    | NunFO.Form f -> convert_formula f

  let convert_model m = NunModel.map ~f:(convert_t_or_f) m
end

module TransFO(T1 : S)(T2 : NunFO.S) = struct
  module Conv = ToFO(T2)
  module ConvBack = OfFO(T1)(T2)

  let pipe =
    NunTransform.make1
    ~name:"to_fo"
    ~encode:(fun pb ->
      let pb' = Conv.convert_problem ~repr:T1.repr pb in
      pb', ()
    )
    ~decode:(fun _st m -> ConvBack.convert_model m)
    ()

  let pipe_with ~decode =
    NunTransform.make1
    ~name:"to_fo"
    ~encode:(fun pb ->
      let pb' = Conv.convert_problem ~repr:T1.repr pb in
      pb', ()
    )
    ~decode:(fun _ x -> decode x)
    ()
end

(** {2 Conversion} *)

let convert
: type t1 t2 inv.
  repr1:(t1,inv) repr ->
  build2:(t2,inv) build ->
  t1 -> t2
= fun ~repr1 ~build2:build t ->
  let rec convert t = match repr1 t with
    | AppBuiltin (b,l) -> app_builtin ~build b (List.map convert l)
    | Const id -> const ~build id
    | Var v -> var ~build (aux_var v)
    | TyVar v -> ty_var ~build (aux_var v)
    | App (f,l) -> app ~build (convert f) (List.map convert l)
    | Bind (b,v,t) -> mk_bind ~build b (aux_var v) (convert t)
    | Let (v,t,u) -> let_ ~build (aux_var v) (convert t) (convert u)
    | Match (t,l) ->
        match_with ~build
          (convert t)
          (ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, convert rhs) l)
    | TyBuiltin b -> ty_builtin ~build b
    | TyArrow (a,b) -> ty_arrow ~build (convert a)(convert b)
    | TyMeta _ -> assert false
  and aux_var v = Var.update_ty ~f:convert v in
  convert t

(** {2 Conversion of UntypedAST to HO, without Type-Checking} *)

module OfUntyped = struct
  module A = NunUntypedAST
  module Loc = NunLocation

  type invariant = <meta:[`NoMeta]; poly:[`Poly]>

  exception Error of A.term * string

  let () = Printexc.register_printer
    (function
      | Error (t,s) ->
          Some (CCFormat.sprintf "of_untyped: error on %a: %s" A.print_term t s)
      | _ -> None
    )

  let error_ t s = raise (Error (t,s))

  type 't env_cell =
    | ID of ID.t
    | Var of 't Var.t

  let convert_term
  : type t. build:(t,invariant) build -> A.term -> t
  = fun ~build t ->
    let env = Hashtbl.create 32 in
    let rec aux t = match Loc.get t with
      | A.App (f, l) ->
          app ~build (aux f) (List.map aux l)
      | A.Wildcard -> error_ t "wildcard not supported"
      | A.Builtin b ->
          let module B = NunBuiltin in
          begin match b with
          | A.Builtin.Prop -> ty_prop ~build
          | A.Builtin.Type -> ty_type ~build
          | A.Builtin.Not -> ty_builtin ~build B.Ty.Prop
          | A.Builtin.And -> builtin ~build B.T.And
          | A.Builtin.Or -> builtin ~build B.T.Or
          | A.Builtin.True -> builtin ~build B.T.True
          | A.Builtin.False -> builtin ~build B.T.False
          | A.Builtin.Imply -> builtin ~build B.T.Imply
          | A.Builtin.Eq | A.Builtin.Equiv ->
              error_ t "unapplied equality"
          end
      | A.AtVar s
      | A.Var s ->
          begin try
            match Hashtbl.find env s with
            | ID id -> const ~build id
            | Var v -> var ~build v
          with Not_found ->
            (* constant, not variable *)
            let id = ID.make ~name:s in
            Hashtbl.add env s (ID id);
            const ~build id
          end
      | A.MetaVar _ -> error_ t "meta variable"
      | A.Exists ((_, None), _)
      | A.Forall ((_, None), _)
      | A.Fun ((_, None), _) -> error_ t "untyped variable"
      | A.Fun ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> fun_ ~build v (aux t))
      | A.Let _ ->
          error_ t "`let` unsupported (no way of inferring the type)"
      | A.Match _ ->
          error_ t "`match` unsupported (no way of inferring the type of variables)"
      | A.Ite (a,b,c) -> ite ~build (aux a) (aux b) (aux c)
      | A.Forall ((v,Some ty),t) ->
          enter_var_ ~ty v (fun v -> forall ~build v (aux t))
      | A.Exists ((v, Some ty),t) ->
          enter_var_ ~ty v (fun v -> exists ~build v (aux t))
      | A.TyArrow (a,b) -> ty_arrow ~build (aux a) (aux b)
      | A.TyForall (v,t) ->
          enter_var_ ~ty:(A.builtin A.Builtin.Type) v
            (fun v -> ty_forall ~build v (aux t))

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
