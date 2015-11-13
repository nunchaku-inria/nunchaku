
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main View for terms} *)

module ID = NunID
module Var = NunVar
module MetaVar = NunMetaVar

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

module Binder = struct
  type t =
    [ `Forall
    | `Exists
    | `Fun
    | `TyForall
    ]

  let to_string = function
    | `Fun -> "fun"
    | `Forall -> "forall"
    | `Exists -> "exists"
    | `TyForall -> "pi"
end

module TyBuiltin = struct
  type t =
    [ `Kind
    | `Type
    | `Prop
    ]
  let equal = (=)
  let to_string = function
    | `Prop -> "prop"
    | `Kind -> "kind"
    | `Type -> "type"
end

(* TODO: parametrize, make 'a Builtin.t, so arity is enforced *)

module Builtin = struct
  type t =
    [ `True
    | `False
    | `Not
    | `Or
    | `And
    | `Imply
    | `Equiv
    | `Ite
    | `Eq
    | `DataTest of id (** Test whether [t : tau] starts with given constructor *)
    | `DataSelect of id * int (** Select n-th argument of given constructor *)
    ]

  let fixity = function
    | `True
    | `False
    | `Ite
    | `Not
    | `DataSelect _
    | `DataTest _ -> `Prefix
    | `Eq
    | `Or
    | `And
    | `Equiv
    | `Imply -> `Infix

  let to_string = function
    | `True -> "true"
    | `False -> "false"
    | `Not -> "~"
    | `Or -> "||"
    | `And -> "&&"
    | `Imply -> "=>"
    | `Equiv
    | `Eq -> "="
    | `DataTest id -> "is-" ^ ID.name id
    | `DataSelect (id, n) -> CCFormat.sprintf "select-%s-%d" (ID.name id) n
    | `Ite -> assert false

  let equal a b = match a, b with
    | `True, `True
    | `False, `False
    | `Not, `Not
    | `Or, `Or
    | `And, `And
    | `Imply, `Imply
    | `Equiv, `Equiv
    | `Ite, `Ite
    | `Eq, `Eq -> true
    | `DataTest id, `DataTest id' -> ID.equal id id'
    | `DataSelect (id, n), `DataSelect (id', n') -> n=n' && ID.equal id id'
    | `True, _
    | `False, _
    | `Ite, _
    | `Not, _
    | `Eq, _
    | `Or, _
    | `And, _
    | `Equiv, _
    | `Imply, _
    | `DataSelect _, _
    | `DataTest _, _ -> false
end

type 'a case = 'a var list * 'a
(** A pattern match case for a given constructor [ vars, right-hand side ]
    The pattern must be linear (variable list does not contain duplicates) *)

(** A list of cases (indexed by constructor) *)
type 'a cases = 'a case ID.Map.t

let cases_to_list = ID.Map.to_list

(* check that: each case is linear (all vars are different) *)
let cases_well_formed (type a) m =
  let is_linear_ _ (vars,_) =
    let module VarSet = Var.Set(struct type t = a end) in
    VarSet.cardinal (VarSet.of_list vars) = List.length vars
  in
  ID.Map.for_all is_linear_ m

(** The main view of terms. Other representations will be refinements
  (read: restrictions) of this view that enforce additional restrictions, such
  as the absence of meta-variables or polymorphism *)
type 'a view =
  | Const of id (** top-level symbol *)
  | Var of 'a var (** bound variable *)
  | App of 'a * 'a list
  | AppBuiltin of Builtin.t * 'a list (** built-in operation *)
  | Bind of Binder.t * 'a var * 'a
  | Let of 'a var * 'a * 'a
  | Match of 'a * 'a cases (** shallow pattern-match *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a  (** Arrow type *)
  | TyMeta of 'a MetaVar.t

(* NOTE: Eq has its own case (in Builtin), because its type parameter is often hidden.
   For instance, when we parse a model back from TPTP or SMT, equalities
   are not annotated with their type parameter; we would have to compute or
   infer types again for an unclear benefit (usually just for printing).

   Instead, we just consider equality  to be a specific "ad-hoc polymorphic"
   predicate and do not require it to have a type argument.
 *)

type 't repr = 't -> 't view
(** A concrete representation of terms by the type [t'] *)

type 't build = 't view -> 't
(** A builder for a concrete representation with type ['t]. *)

module type REPR = sig
  type t
  val repr : t repr
end

module type BUILD = sig
  type t
  val build : t build
end

module type S = sig
  type t
  include REPR with type t := t
  include BUILD with type t := t
end

(** {2 Printing} *)

module type PRINT = sig
  type t
  val print : t printer
  val print_in_app : t printer
  val print_in_binder : t printer
end

module Print(T : REPR)
: PRINT with type t = T.t
= struct
  type t = T.t

  let fpf = Format.fprintf
  let pp_list_ ?(start="") ?(stop="") ~sep pp =
    CCFormat.list ~start ~stop ~sep pp

  let rec print out t = match T.repr t with
    | TyBuiltin b -> CCFormat.string out (TyBuiltin.to_string b)
    | Const id -> ID.print_no_id out id
    | TyMeta v -> NunMetaVar.print out v
    | Var v -> Var.print out v
    | AppBuiltin (`Ite, [a;b;c]) ->
        fpf out "@[<2>if %a@ then %a@ else %a@]"
          print a print b print c
    | AppBuiltin (`DataTest c, [t]) ->
        fpf out "@[<2>is-%a@ %a@]" ID.print_name c print_in_app t
    | AppBuiltin (`DataSelect (c,n), [t]) ->
        fpf out "@[<2>select-%a-%d@ %a@]" ID.print_name c n print_in_app t
    | AppBuiltin (b, []) -> CCFormat.string out (Builtin.to_string b)
    | AppBuiltin (f, [a;b]) when Builtin.fixity f = `Infix ->
        fpf out "@[<hv>%a@ %s@ %a@]"
          print_in_app a (Builtin.to_string f) print_in_app b
    | AppBuiltin (b,l) ->
        fpf out "@[<2>%s@ %a@]" (Builtin.to_string b)
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
        let s = Binder.to_string b in
        fpf out "@[<2>%s %a:%a.@ %a@]" s Var.print v print_in_app (Var.ty v) print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_binder a print b
  and print_in_app out t = match T.repr t with
    | AppBuiltin (_,[]) | TyBuiltin _ | Const _ -> print out t
    | TyMeta _ -> print out t
    | Var _ -> print out t
    | App (_,_) | AppBuiltin (_,_::_)
    | Let _ | Match _ -> fpf out "(@[%a@])" print t
    | Bind _ -> fpf out "(@[%a@])" print t
    | TyArrow (_,_) -> fpf out "(@[%a@])" print t
  and print_in_binder out t = match T.repr t with
    | TyBuiltin _ | Const _ | App (_,_) | AppBuiltin _ ->
        print out t
    | Var _ -> print out t
    | TyMeta _ -> print out t
    | Bind _ -> fpf out "(@[%a@])" print t
    | Let _ | Match _ | TyArrow (_,_) -> fpf out "(@[%a@])" print t
end

type 'a print = (module PRINT with type t = 'a)

(** {2 Utils} *)

module type UTIL_REPR = sig
  type t_

  val head_sym : t_ -> id
  (** Search for a head symbol
      @raise Not_found if not an application/const *)

  val to_seq : t_ -> t_ Sequence.t
  (** Iterate on sub-terms *)

  val to_seq_vars : t_ -> t_ Var.t Sequence.t
  (** Iterate on variables *)

  val to_seq_free_vars : t_ -> t_ Var.t Sequence.t
  (** Iterate on free variables. *)

  val free_meta_vars : ?init:t_ MetaVar.t ID.Map.t -> t_ -> t_ MetaVar.t ID.Map.t
  (** The free type meta-variables in [t] *)

  val ty_is_Type : t_ -> bool
  (** t == Type? *)

  val ty_returns_Type : t_ -> bool
  (** t == forall ... -> ... -> ... -> Type? *)

  val ty_returns : t_ -> t_
  (** follow forall/arrows to get return type.  *)

  val ty_is_Kind : t_ -> bool
  (** type == Kind? *)

  val ty_num_param : t_ -> int
end

(** Utils that only require a {!REPR} *)
module UtilRepr(T : REPR)
: UTIL_REPR with type t_ = T.t
= struct
  type t_ = T.t

  let rec head_sym t = match T.repr t with
    | App (f, _) -> head_sym f
    | Const id -> id
    | _ -> raise Not_found

  let to_seq t yield =
    let rec aux t =
      yield t;
      match T.repr t with
      | TyMeta _ -> ()
      | TyBuiltin _
      | AppBuiltin _
      | Const _ -> ()
      | Var v -> aux_var v
      | Match (t,l) ->
          aux t;
          ID.Map.iter (fun _ (vars,rhs) -> List.iter aux_var vars; aux rhs) l
      | App (f,l) -> aux f; List.iter aux l
      | Bind (_,v,t) -> aux (Var.ty v); aux t
      | Let (v,t,u) -> aux (Var.ty v); aux t; aux u
      | TyArrow (a,b) -> aux a; aux b
    and aux_var v = aux (Var.ty v)
    in
    aux t

  let to_seq_free_vars t yield =
    let module VarSet = Var.Set(T) in
    let rec aux ~bound t = match T.repr t with
      | Const _ -> ()
      | Var v ->
          if VarSet.mem v bound then () else yield v
      | App (f,l) ->
          aux ~bound f; List.iter (aux ~bound) l
      | Match (t,l) ->
          aux ~bound t;
          ID.Map.iter
            (fun _ (vars,rhs) ->
              let bound = List.fold_right VarSet.add vars bound in
              aux ~bound rhs
            ) l
      | AppBuiltin (_,l) -> List.iter (aux ~bound) l
      | Bind (_,v,t) -> aux ~bound:(VarSet.add v bound) t
      | Let (v,t,u) -> aux ~bound t; aux ~bound:(VarSet.add v bound) u
      | TyBuiltin _ -> ()
      | TyArrow (a,b) -> aux ~bound a; aux ~bound b
      | TyMeta _ -> ()
    in
    aux ~bound:VarSet.empty t

  let to_seq_vars t =
    to_seq t
    |> Sequence.flat_map
        (fun t -> match T.repr t with
          | Var v
          | Bind (_,v,_)
          | Let (v,_,_) -> Sequence.return v
          | Match (_,l) ->
              let open Sequence.Infix in
              ID.Map.to_seq l >>= fun (_,(vars,_)) -> Sequence.of_list vars
          | AppBuiltin _
          | Const _
          | App _
          | TyBuiltin _
          | TyArrow (_,_)
          | TyMeta _ -> Sequence.empty
        )

  let to_seq_meta_vars t =
    to_seq t
    |> Sequence.filter_map
        (fun t -> match T.repr t with
          | TyMeta v -> Some v
          | Var _
          | Bind _
          | AppBuiltin _
          | Const _
          | Let _
          | Match _
          | App _
          | TyBuiltin _
          | TyArrow (_,_) -> None
        )

  let free_meta_vars ?(init=ID.Map.empty) t =
    to_seq_meta_vars t
      |> Sequence.fold
          (fun acc v -> ID.Map.add (NunMetaVar.id v) v acc)
          init

  let ty_is_Type t = match T.repr t with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_is_Kind t = match T.repr t with
    | TyBuiltin `Kind -> true
    | _ -> false

  let rec ty_returns t = match T.repr t with
    | TyArrow (_, t') -> ty_returns t'
    | Bind (`TyForall, _, t') -> ty_returns t'
    | _ -> t

  let ty_returns_Type t = match T.repr (ty_returns t) with
    | TyBuiltin `Type -> true
    | _ -> false

  (* number of parameters of this (polymorphic?) T.t type *)
  let rec ty_num_param ty = match T.repr ty with
    | TyMeta _ -> 0
    | Var _ -> 0
    | Const _
    | App _
    | TyBuiltin _ -> 0
    | TyArrow (_,t') ->
        if ty_is_Type t'
          then 1 + ty_num_param t'
          else 0  (* asks for term parameters *)
    | Bind (`TyForall, _,t) -> 1 + ty_num_param t
    | _ -> assert false
end

exception Undefined of id
(** When a symbol is not defined *)

let () = Printexc.register_printer
  (function
    | Undefined id -> Some ("undefined ID: " ^ ID.to_string id)
    | _ -> None
  )

module type UTIL = sig
  include UTIL_REPR

  val const : id -> t_
  val builtin : Builtin.t -> t_
  val app_builtin : Builtin.t -> t_ list -> t_
  val var : t_ var -> t_
  val app : t_ -> t_ list -> t_
  val fun_ : t_ var -> t_ -> t_
  val let_ : t_ var -> t_ -> t_ -> t_
  val match_with : t_ -> t_ cases -> t_
  val ite : t_ -> t_ -> t_ -> t_
  val forall : t_ var -> t_ -> t_
  val exists : t_ var -> t_ -> t_
  val eq : t_ -> t_ -> t_

  val mk_bind : Binder.t -> t_ var -> t_ -> t_

  val ty_type : t_ (** Type of types *)
  val ty_kind : t_ (** Type of ty_type *)
  val ty_prop : t_ (** Propositions *)

  val ty_builtin : TyBuiltin.t -> t_
  val ty_const : id -> t_
  val ty_app : t_ -> t_ list -> t_
  val ty_arrow : t_ -> t_ -> t_
  val ty_var : t_ var -> t_
  val ty_meta : t_ MetaVar.t -> t_
  val ty_forall : t_ var -> t_ -> t_

  (** {6 Substitution Utils} *)

  type subst = (t_, t_) Var.Subst.t

  val equal : subst:subst -> t_ -> t_ -> bool
  (** Equality modulo substitution *)

  val deref : subst:subst -> t_ -> t_
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  exception ApplyError of string * t_ * t_ list
  (** Raised when a type application fails *)

  val eval : subst:subst -> t_ -> t_
  (** Applying a substitution *)

  val ty_apply : t_ -> t_ list -> t_
  (** [apply t l] computes the type of [f args] where [f : t] and [args : l].
      @raise ApplyError if the arguments do not match *)

  val ty_apply_full : t_ -> t_ list -> t_ * subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  type signature = id -> t_ option
  (** A signature is a way to obtain the type of a variable *)

  val ty : sigma:signature -> t_ -> t_ or_error
  (** Compute the type of the given term in the given signature. *)

  val ty_exn : sigma:signature -> t_ -> t_
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Undefined in case some symbol is not defined *)

  exception UnifError of string * t_ * t_
  (** Raised for unification or matching errors *)

  val match_exn : ?subst2:subst -> t_ -> t_ -> subst
  (** [match_exn ~subst2 t1 t2] matches the pattern [t1] against [subst2 t2].
      Variables in [subst2 t2] are not bound.
      We assume [t1] and [subst2 t2] do not share variables, and we assume
      that [t1] is a mostly first-order {b pattern} (no binders, but variables
      in head position is accepted and will only match an application).
      @raise UnifError if they dont_ match
      @raise Invalid_argument if [t1] is not a valid pattern *)

  val match_ : ?subst2:subst -> t_ -> t_ -> subst option
  (** Safe version of {!match_exn}
      @raise Invalid_argument if [t1] is not a valid pattern *)

  (* TODO: unification *)
end

module Util(T : S)
: UTIL with type t_ = T.t
= struct
  include UtilRepr(T)

  let ty_type = T.build (TyBuiltin `Type)
  let ty_kind = T.build (TyBuiltin `Kind)
  let ty_prop = T.build (TyBuiltin `Prop)

  let app_builtin s l = T.build (AppBuiltin (s,l))
  let builtin s = app_builtin s []
  let const id = T.build (Const id)
  let var v = T.build (Var v)
  let app t l = T.build (App(t,l))
  let mk_bind b v t = T.build (Bind (b,v,t))
  let fun_ v t = T.build (Bind (`Fun,v, t))
  let let_ v t u = T.build (Let (v, t, u))
  let match_with t l =
    if ID.Map.is_empty l then invalid_arg "Term.case: empty list of cases";
    T.build (Match (t,l))
  let ite a b c =
    app (builtin `Ite) [a;b;c]
  let forall v t = T.build (Bind(`Forall,v, t))
  let exists v t = T.build (Bind(`Exists,v, t))
  let eq a b = app (builtin `Eq) [a;b]

  let ty_builtin b = T.build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l = if l=[] then f else app f l
  let ty_arrow a b = T.build (TyArrow (a,b))
  let ty_forall v t = T.build (Bind (`TyForall,v,t))
  let ty_var v = T.build (Var v)
  let ty_meta v = T.build (TyMeta v)

  module Subst = Var.Subst

  type subst = (T.t, T.t) Subst.t

  let rec equal ~subst ty1 ty2 =
    match T.repr ty1, T.repr ty2 with
    | Const id1, Const id2 -> ID.equal id1 id2
    | Var v1, _ when Subst.mem ~subst v1 ->
        equal ~subst (Subst.find_exn ~subst v1) ty2
    | _, Var v2 when Subst.mem ~subst v2 ->
        equal ~subst ty1 (Subst.find_exn ~subst v2)
    | Var v1, Var v2 -> Var.equal v1 v2
    | AppBuiltin (b1,l1), AppBuiltin (b2,l2) ->
        Builtin.equal b1 b2 &&
        List.length l1 = List.length l2 &&
        List.for_all2 (equal ~subst) l1 l2
    | TyBuiltin b1, TyBuiltin b2 -> TyBuiltin.equal b1 b2
    | TyMeta v1, TyMeta v2 -> MetaVar.equal v1 v2
    | App (f1,l1), App (f2, l2) ->
        equal ~subst f1 f2
          && List.length l1 = List.length l2
          && List.for_all2 (equal ~subst) l1 l2
    | TyArrow (a1,b1), TyArrow (a2,b2) ->
        equal ~subst a1 a2 && equal ~subst b1 b2
    | Bind (b1, v1, t1), Bind (b2, v2, t2) ->
        b1 = b2 &&
        ( let v = Var.fresh_copy v1 in
          let subst = Subst.add ~subst v1 (var v) in
          let subst = Subst.add ~subst v2 (var v) in
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
                let subst = Subst.add ~subst v1 (var v) in
                let subst = Subst.add ~subst v2 (var v) in
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
    | TyArrow (_,_),_
    | Bind _, _
    | TyMeta _,_ -> false

  let rec deref ~subst t = match T.repr t with
    | Var v ->
        begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
        end
    | _ -> t

  (* NOTE: when dependent types are added, substitution in types is needed *)

  let rec eval ~subst t = match T.repr t with
    | TyMeta _ -> t
    | Const _
    | TyBuiltin _ -> t
    | AppBuiltin (_,[]) -> t
    | AppBuiltin (b,l) ->
        app_builtin b (List.map (eval ~subst) l)
    | Bind (b, v, t) ->
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (var v') in
        mk_bind b v' (eval ~subst t)
    | Let (v,t,u) ->
        let v' = Var.fresh_copy v in
        let t = eval ~subst t in
        let subst = Subst.add ~subst v (var v') in
        let_ v' t (eval ~subst u)
    | Match (t,l) ->
        let t = eval ~subst t in
        let l = ID.Map.map
          (fun (vars,rhs) ->
            let vars' = Var.fresh_copies vars in
            let subst = Subst.add_list ~subst vars (List.map var vars') in
            vars', eval ~subst rhs
          ) l
        in
        match_with t l
    | Var v -> CCOpt.get t (Subst.find ~subst v)
    | App (f,l) ->
        app (eval ~subst f) (List.map (eval ~subst) l)
    | TyArrow (a,b) ->
        ty_arrow (eval ~subst a) (eval ~subst b)

  exception ApplyError of string * T.t * T.t list
  (** Raised when a type application fails *)

  exception UnifError of string * T.t * T.t
  (** Raised for unification or matching errors *)

  let () =
    Printexc.register_printer
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
    let rec app_ ~subst t l = match T.repr t, l with
      | _, [] -> t, subst
      | TyBuiltin _, _
      | App (_,_),_
      | Const _, _ ->
          error_apply_ "cannot apply this type" ~hd:t ~l
      | Var v, _ ->
          begin try
            let t = Subst.find_exn ~subst v in
            app_ ~subst t l
          with Not_found ->
            error_apply_ "cannot apply this type" ~hd:t ~l
          end
      | TyMeta _,_ -> assert false
      | TyArrow (a, t'), b :: l' ->
          if equal ~subst a b
          then app_ ~subst t' l'
          else error_apply_
            "type mismatch on first argument" ~hd:t ~l
      | Bind (`TyForall, v,t'), b :: l' ->
          let subst = Subst.add ~subst v b in
          app_ ~subst t' l'
      | _ -> assert false
    in
    app_ ~subst:Subst.empty t l

  let ty_apply t l =
    let t, subst = ty_apply_full t l in
    if Subst.is_empty subst then t else eval ~subst t

  let rec get_ty_arg_ ty i = match T.repr ty with
    | App (_,_)
    | TyBuiltin _
    | Const _
    | Var _
    | TyMeta _ -> None
    | TyArrow (a,b) ->
        if i=0 then Some a else get_ty_arg_ b (i-1)
    | Bind (`TyForall, _,_) -> None
    | _ -> assert false

  type signature = id -> T.t option

  let find_ty_ ~sigma id = match sigma id with
    | Some ty -> ty
    | None -> raise (Undefined id)

  let rec ty_exn ~sigma t = match T.repr t with
    | Const id -> find_ty_ ~sigma id
    | AppBuiltin (b,_) ->
        let prop = ty_prop in
        let prop1 = ty_arrow prop prop in
        let prop2 = ty_arrow prop (ty_arrow prop prop) in
        begin match b with
          | `Equiv
          | `Imply
          | `Or
          | `And -> prop2
          | `Not -> prop1
          | `True
          | `False
          | `Ite
          | `Eq -> prop
          | `DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = find_ty_ ~sigma id in
              ty_arrow (ty_returns ty) prop
          | `DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = find_ty_ ~sigma id in
              begin match get_ty_arg_ ty n with
              | None ->
                  failwith "cannot infer type, wrong argument to DataSelect"
              | Some ty_arg ->
                  ty_arrow (ty_returns ty) ty_arg
              end
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        ty_apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
    | Bind (b,v,t) ->
        begin match b with
        | `Forall
        | `Exists -> ty_arrow (Var.ty v) ty_prop
        | `Fun ->
            if ty_returns_Type (Var.ty v)
            then ty_forall v (ty_exn ~sigma t)
            else ty_arrow (Var.ty v) (ty_exn ~sigma t)
        | `TyForall -> ty_type
        end
    | Let (_,_,u) -> ty_exn ~sigma u
    | Match (_,m) ->
        let _, (_, rhs) = ID.Map.choose m in
        ty_exn ~sigma rhs
    | TyMeta _ -> assert false
    | TyBuiltin b ->
        begin match b with
        | `Kind -> failwith "Term_ho.ty: kind has no type"
        | `Type -> ty_kind
        | `Prop -> ty_type
        end
    | TyArrow (_,_) -> ty_type

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
      f1::l1, (app f2 l2_1) :: l2_2
    else
      let l1_1, l1_2 = CCList.take_drop (n1-n2) l1 in
      (app f1 l1_1) :: l1_2, f2 :: l2

  let match_exn ?(subst2=Subst.empty) t1 t2 =
    (* bound: bound variables in t1 and t2 *)
    let rec match_ subst t1 t2 =
      let t2 = deref ~subst:subst2 t2 in
      match T.repr t1, T.repr t2 with
      | AppBuiltin (b1,l1), AppBuiltin (b2,l2)
          when Builtin.equal b1 b2 && List.length l1 = List.length l2 ->
            List.fold_left2 match_ subst l1 l2
      | Const id1, Const id2 when ID.equal id1 id2 -> subst
      | Var v1, _ -> match_var subst v1 t1 t2
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
      | TyBuiltin b1, TyBuiltin b2 when TyBuiltin.equal b1 b2 -> subst
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

(** {2 Default Implementation} *)

module Default : S
= struct
  type t = {
    view: t view;
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

let default = (module Default : S)

(** {2 Conversion between two representations} *)

module Convert(T1 : REPR)(T2 : BUILD)
: sig
  val convert : T1.t -> T2.t
end = struct
  let rec convert t = T2.build
    ( match T1.repr t with
      | TyBuiltin b -> TyBuiltin b
      | Const id -> Const id
      | AppBuiltin (b,l) -> AppBuiltin (b, List.map convert l)
      | Var v -> Var (aux_var v)
      | App (f,l) -> App (convert f, List.map convert l)
      | Bind (b,v,t) -> Bind (b, aux_var v, convert t)
      | Let (v,t,u) -> Let (aux_var v, convert t, convert u)
      | Match (t,l) ->
          Match (
            convert t,
            ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, convert rhs) l
          )
      | TyArrow (a,b) -> TyArrow (convert a, convert b)
      | TyMeta v -> TyMeta (aux_meta v)
    )
  and aux_var v = Var.update_ty ~f:convert v
  and aux_meta v = MetaVar.update ~f:convert v
end
