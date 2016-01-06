
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main View for terms} *)

module ID = ID
module Var = Var
module MetaVar = MetaVar

type id = ID.t
type 'a var = 'a Var.t
type 'a or_error = [`Ok of 'a | `Error of string]
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

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

module Builtin = struct
  type 'a t =
    [ `True
    | `False
    | `Not
    | `Or
    | `And
    | `Imply
    | `Equiv of 'a * 'a
    | `Ite of 'a * 'a * 'a
    | `Eq of 'a * 'a
    | `DataTest of id (** Test whether [t : tau] starts with given constructor *)
    | `DataSelect of id * int (** Select n-th argument of given constructor *)
    | `Undefined of id * 'a (** Undefined case. argument=the undefined term *)
    ]

  let is_infix = function
    | `Eq _ | `Or | `And | `Equiv _ | `Imply -> true
    | _ -> false

  let pp pterm out = function
    | `True -> CCFormat.string out "true"
    | `False -> CCFormat.string out "false"
    | `Not -> CCFormat.string out "~"
    | `Or -> CCFormat.string out "||"
    | `And -> CCFormat.string out "&&"
    | `Imply -> CCFormat.string out "=>"
    | `Equiv (a,b) | `Eq (a,b) ->
        fpf out "@[<hv>%a@ @[<hv>=@ %a@]@]" pterm a pterm b
    | `Ite (a,b,c) ->
        fpf out "@[<hv>@[<2>if@ %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
          pterm a pterm b pterm c
    | `DataTest id -> fpf out "is-%s" (ID.name id)
    | `DataSelect (id, n) ->
        fpf out "select-%s-%d" (ID.name id) n
    | `Undefined (id,_) -> fpf out "undefined_%d" (ID.id id)

  let equal
  : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  = fun eqterm a b -> match a, b with
    | `True, `True
    | `False, `False
    | `Not, `Not
    | `Or, `Or
    | `And, `And
    | `Imply, `Imply -> true
    | `Ite(a1,b1,c1), `Ite(a2,b2,c2) ->
        eqterm a1 a2 && eqterm b1 b2 && eqterm c1 c2
    | `Equiv (a1,b1), `Equiv(a2,b2)
    | `Eq(a1,b1), `Eq (a2,b2) -> eqterm a1 a2 && eqterm b1 b2
    | `DataTest id, `DataTest id' -> ID.equal id id'
    | `DataSelect (id, n), `DataSelect (id', n') -> n=n' && ID.equal id id'
    | `Undefined (a,t1), `Undefined (b,t2) -> ID.equal a b && eqterm t1 t2
    | `True, _ | `False, _ | `Ite _, _ | `Not, _
    | `Eq _, _ | `Or, _ | `And, _ | `Equiv _, _ | `Imply, _
    | `DataSelect _, _ | `DataTest _, _ | `Undefined _, _ -> false

  let map : f:('a -> 'b) -> 'a t -> 'b t
  = fun ~f b -> match b with
    | `True -> `True
    | `False -> `False
    | `And -> `And
    | `Imply -> `Imply
    | `Ite (a,b,c) -> `Ite (f a, f b, f c)
    | `Eq (a,b) -> `Eq (f a, f b)
    | `Equiv (a,b) -> `Equiv (f a, f b)
    | `DataTest id -> `DataTest id
    | `Or -> `Or
    | `Not -> `Not
    | `DataSelect (c,n) -> `DataSelect (c,n)
    | `Undefined (id, t) -> `Undefined (id, f t)

  let fold : f:('acc -> 'a -> 'acc) -> x:'acc -> 'a t -> 'acc
  = fun ~f ~x:acc b -> match b with
    | `True
    | `And
    | `Imply
    | `False
    | `Or
    | `DataTest _
    | `DataSelect _
    | `Not -> acc
    | `Ite (a,b,c) -> f (f (f acc a) b) c
    | `Eq (a,b)
    | `Equiv (a,b) -> f (f acc a) b
    | `Undefined (_,t) -> f acc t

  let fold2 :
      f:('acc -> 'a -> 'b -> 'acc) -> fail:(unit -> 'acc) ->
        x:'acc -> 'a t -> 'b t -> 'acc
  = fun ~f ~fail ~x:acc b1 b2 -> match b1, b2 with
    | `True, `True
    | `And, `And
    | `Imply, `Imply
    | `False, `False
    | `Not, `Not
    | `Or, `Or -> acc
    | `DataTest i1, `DataTest i2 -> if ID.equal i1 i2 then acc else fail()
    | `DataSelect (i1,n1), `DataSelect (i2,n2) ->
        if n1=n2 && ID.equal i1 i2 then acc else fail()
    | `Ite (a1,b1,c1), `Ite(a2,b2,c2) ->
        let acc = f acc a1 a2 in
        let acc = f acc b1 b2 in
        f acc c1 c2
    | `Eq (a1,b1), `Eq (a2,b2)
    | `Equiv (a1,b1), `Equiv (a2,b2) -> let acc = f acc a1 a2 in f acc b1 b2
    | `Undefined (i1,t1), `Undefined (i2,t2) ->
        if ID.equal i1 i2 then f acc t1 t2 else fail()
    | `True, _ | `False, _ | `Ite _, _ | `Not, _
    | `Eq _, _ | `Or, _ | `And, _ | `Equiv _, _ | `Imply, _
    | `DataSelect _, _ | `DataTest _, _ | `Undefined _, _ -> fail()



  let iter : ('a -> unit) -> 'a t -> unit
  = fun f b -> match b with
    | `True
    | `And
    | `Imply
    | `False
    | `Or
    | `DataTest _
    | `DataSelect _
    | `Not -> ()
    | `Ite (a,b,c) -> f a; f b; f c
    | `Eq (a,b)
    | `Equiv (a,b) -> f a; f b
    | `Undefined (_,t) -> f t

  let to_seq b f = iter f b
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
  | Builtin of 'a Builtin.t (** built-in operation *)
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

  let pp_list_ ?(start="") ?(stop="") ~sep pp =
    CCFormat.list ~start ~stop ~sep pp

  let is_if_ t = match T.repr t with
    | Builtin (`Ite _) -> true
    | _ -> false

  let rec unroll_if_ t = match T.repr t with
    | Builtin (`Ite (a,b,c)) ->
        let l, last = unroll_if_ c in
        (a,b) :: l, last
    | _ -> [], t

  let rec print out t = match T.repr t with
    | TyBuiltin b -> CCFormat.string out (TyBuiltin.to_string b)
    | Const id -> ID.print out id
    | TyMeta v -> MetaVar.print out v
    | Var v -> Var.print_full out v
    | Builtin (`Ite (a,b,c)) when is_if_ c ->
        (* special case to avoid deep nesting of ifs *)
        let pp_middle out (a,b) =
          fpf out "@[<2>else if@ @[%a@]@]@ @[<2>then@ @[%a@]@]" print a print b
        in
        let middle, last = unroll_if_ c in
        assert (not (is_if_ last));
        fpf out "@[<hv>@[<2>if@ @[%a@]@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
          print a print b
          (pp_list_ ~sep:"" pp_middle) middle
          print last
    | Builtin b -> Builtin.pp print_in_app out b
    | App (f,l) ->
        begin match T.repr f with
        | Builtin b when Builtin.is_infix b ->
            fpf out "@[<hv>%a@]" (print_infix_list b) l
        | _ ->
            fpf out "@[<2>%a@ %a@]" print_in_app f
              (pp_list_ ~sep:" " print_in_app) l
        end
    | Let (v,t,u) ->
        fpf out "@[<2>let %a :=@ %a in@ %a@]" Var.print_full v print t print u
    | Match (t,l) ->
        let pp_case out (id,(vars,t)) =
          fpf out "@[<hv2>| @[<hv2>%a %a@] ->@ %a@]"
            ID.print id (pp_list_ ~sep:" " Var.print_full) vars print t
        in
        fpf out "@[<hv>@[<hv2>match @[%a@] with@ %a@]@ end@]"
          print t (pp_list_ ~sep:"" pp_case) (ID.Map.to_list l)
    | Bind (b, v, t) ->
        let s = Binder.to_string b in
        fpf out "@[<2>%s %a:%a.@ %a@]" s Var.print_full v print_in_app (Var.ty v) print t
    | TyArrow (a,b) ->
        fpf out "@[<2>%a ->@ %a@]" print_in_binder a print b
  and print_in_app out t = match T.repr t with
    | Builtin b when not (Builtin.is_infix b) -> print out t
    | TyBuiltin _ | Const _ -> print out t
    | TyMeta _ -> print out t
    | Var _ -> print out t
    | App (_,_) | Builtin _
    | Let _ | Match _ -> fpf out "(@[%a@])" print t
    | Bind _ -> fpf out "(@[%a@])" print t
    | TyArrow (_,_) -> fpf out "(@[%a@])" print t
  and print_in_binder out t = match T.repr t with
    | TyBuiltin _ | Const _ | App (_,_) | Builtin _ ->
        print out t
    | Var _ -> print out t
    | TyMeta _ -> print out t
    | Bind _ -> fpf out "(@[%a@])" print t
    | Let _ | Match _ | TyArrow (_,_) -> fpf out "(@[%a@])" print t
  and print_infix_list b out l = match l with
    | [] -> assert false
    | [t] -> print_in_app out t
    | t :: l' ->
        fpf out "@[%a@]@ @[%a@] %a"
          print_in_app t (Builtin.pp print_in_app) b (print_infix_list b) l'
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

  val ty_unfold : t_ -> t_ Var.t list * t_ list * t_
  (** [ty_unfold ty] decomposes [ty] into a list of quantified type variables,
      a list of parameters, and a return type (which is not an arrow).

      [ty_unfold (forall a b, a -> b -> c -> d)] will return
      [([a;b], [a;b;c], d)]
  *)

  val ty_is_Type : t_ -> bool
  (** t == Type? *)

  val ty_returns_Type : t_ -> bool
  (** t == forall ... -> ... -> ... -> Type? *)

  val ty_returns_Prop : t_ -> bool

  val ty_returns : t_ -> t_
  (** follow forall/arrows to get return type.  *)

  val ty_is_Kind : t_ -> bool
  (** type == Kind? *)

  val ty_is_Prop : t_ -> bool
  (** t == Prop? *)

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
      | Const _ -> ()
      | Var v -> aux_var v
      | Match (t,l) ->
          aux t;
          ID.Map.iter (fun _ (vars,rhs) -> List.iter aux_var vars; aux rhs) l
      | Builtin b -> Builtin.iter aux b
      | App (f,l) -> aux f; List.iter aux l
      | Bind (_,v,t) -> aux_var v; aux t
      | Let (v,t,u) -> aux_var v; aux t; aux u
      | TyArrow (a,b) -> aux a; aux b
    and aux_var v = aux (Var.ty v)
    in
    aux t

  let to_seq_free_vars t yield =
    let module VarSet = Var.Set(T) in
    let rec aux ~bound t = match T.repr t with
      | Const _ -> ()
      | Var v ->
          if VarSet.mem v bound then () else yield v;
          aux ~bound (Var.ty v)
      | App (f,l) ->
          aux ~bound f; List.iter (aux ~bound) l
      | Match (t,l) ->
          aux ~bound t;
          ID.Map.iter
            (fun _ (vars,rhs) ->
              List.iter (fun v -> aux ~bound (Var.ty v)) vars;
              let bound = List.fold_right VarSet.add vars bound in
              aux ~bound rhs
            ) l
      | Builtin b -> Builtin.iter (aux ~bound) b
      | Bind (_,v,t) ->
          aux ~bound (Var.ty v); aux ~bound:(VarSet.add v bound) t
      | Let (v,t,u) ->
          aux ~bound (Var.ty v); aux ~bound t; aux ~bound:(VarSet.add v bound) u
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
          | Builtin _
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
          | Builtin _
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
          (fun acc v -> ID.Map.add (MetaVar.id v) v acc)
          init

  let ty_unfold t =
    let rec aux1 t = match T.repr t with
      | TyArrow (l, r) ->
          let args, ret = aux2 r in
          [], l :: args, ret
      | Bind (`TyForall, v, t') ->
          let vs, args, ret = aux1 t' in
          v :: vs, args, ret
      | _ -> [], [], t
    and aux2 t = match T.repr t with
      | TyArrow (l, r) ->
          let args, ret = aux2 r in
          l :: args, ret
      | _ -> [], t
    in
    aux1 t

  let ty_is_Type t = match T.repr t with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_is_Kind t = match T.repr t with
    | TyBuiltin `Kind -> true
    | _ -> false

  let ty_is_Prop t = match T.repr t with
    | TyBuiltin `Prop -> true
    | _ -> false

  let rec ty_returns t = match T.repr t with
    | TyArrow (_, t') -> ty_returns t'
    | Bind (`TyForall, _, t') -> ty_returns t'
    | _ -> t

  let ty_returns_Type t = match T.repr (ty_returns t) with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_returns_Prop t = match T.repr (ty_returns t) with
    | TyBuiltin `Prop -> true
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
  val builtin : t_ Builtin.t -> t_
  val app_builtin : t_ Builtin.t -> t_ list -> t_
  val var : t_ var -> t_
  val app : t_ -> t_ list -> t_
  val fun_ : t_ var -> t_ -> t_
  val let_ : t_ var -> t_ -> t_ -> t_
  val match_with : t_ -> t_ cases -> t_
  val ite : t_ -> t_ -> t_ -> t_
  val forall : t_ var -> t_ -> t_
  val exists : t_ var -> t_ -> t_

  val eq : t_ -> t_ -> t_
  val equiv : t_ -> t_ -> t_
  val imply : t_ -> t_ -> t_
  val true_ : t_
  val false_ : t_
  val and_ : t_ list -> t_
  val or_ : t_ list -> t_
  val not_ : t_ -> t_
  val undefined_ : t_ -> t_ (** fresh undefined term *)
  val data_test : ID.t -> t_ -> t_
  val data_select : ID.t -> int -> t_ -> t_

  val mk_bind : Binder.t -> t_ var -> t_ -> t_

  val ty_type : t_ (** Type of types *)
  val ty_kind : t_ (** Type of ty_type *)
  val ty_prop : t_ (** Propositions *)

  val ty_builtin : TyBuiltin.t -> t_
  val ty_const : id -> t_
  val ty_app : t_ -> t_ list -> t_
  val ty_arrow : t_ -> t_ -> t_
  val ty_arrow_l : t_ list -> t_ -> t_
  val ty_var : t_ var -> t_
  val ty_meta : t_ MetaVar.t -> t_
  val ty_forall : t_ var -> t_ -> t_

  val hash : t_ -> int
  (** Hash into a positive integer *)

  val equal : t_ -> t_ -> bool
  (** Syntactic equality *)

  (** {6 Substitution Utils} *)

  type subst = (t_, t_) Var.Subst.t

  val equal_with : subst:subst -> t_ -> t_ -> bool
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

  let const id = T.build (Const id)
  let var v = T.build (Var v)
  let app t l = T.build (App(t,l))
  let mk_bind b v t = T.build (Bind (b,v,t))
  let fun_ v t = T.build (Bind (`Fun,v, t))

  let let_ v t u = match T.repr u with
    | Builtin `True
    | Builtin `False -> u
    | _ -> T.build (Let (v, t, u))

  let match_with t l =
    if ID.Map.is_empty l then invalid_arg "Term.case: empty list of cases";
    T.build (Match (t,l))

  let forall v t = T.build (Bind(`Forall,v, t))
  let exists v t = T.build (Bind(`Exists,v, t))

  let flatten (b:[<`And | `Or]) l =
    CCList.flat_map
      (fun t -> match T.repr t with
        | Builtin `True when b=`And -> []
        | Builtin `False when b=`Or -> []
        | App (f, l') ->
            begin match T.repr f with
            | Builtin `Or when b=`Or -> l'
            | Builtin `And when b=`And -> l'
            | _ -> [t]
            end
        | _ -> [t])
      l

  let builtin_ b = T.build (Builtin b)
  let app_builtin_ b l = app (builtin_ b) l

  let true_ = builtin_ `True
  let false_ = builtin_ `False

  let rec builtin arg = match arg with
    | `Ite (a,b,c) ->
        begin match T.repr a, T.repr b, T.repr c with
        | Builtin `True, _, _ -> b
        | Builtin `False, _, _ -> c
        | _, Builtin `True, Builtin `False -> a
        | _, Builtin `False, Builtin `True -> not_ a
        | _, Builtin `True, Builtin `True -> true_
        | _, Builtin `False, Builtin `False -> false_
        | _ -> builtin_ arg
        end
    | `Equiv (a,b) ->
        begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | _, Builtin `True -> a
        | Builtin `False, _ -> not_ b
        | _, Builtin `False -> not_ a
        | _ -> builtin_ arg
        end
    | _ -> builtin_ arg

  and app_builtin arg l = match arg, l with
    | `And, _ ->
        begin match flatten `And l with
        | [] -> true_
        | [x] -> x
        | l -> app_builtin_ `And l
        end
    | `Or, _ ->
        begin match flatten `Or l with
        | [] -> false_
        | [x] -> x
        | l -> app_builtin_ `Or l
        end
    | `Not, [t] ->
        begin match T.repr t with
        | Builtin `True -> false_
        | Builtin `False -> true_
        | App (f, l) ->
            begin match T.repr f, l with
            | Builtin `And, _ -> or_ (List.map not_ l)
            | Builtin `Or, _ -> and_ (List.map not_ l)
            | Builtin `Not, [t] -> t
            | _ -> app_builtin_ `Not [t]
            end
        | _ -> app_builtin_ `Not [t]
        end
    | `Imply, [a;b] ->
        begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | Builtin `False, _ -> true_
        | _, Builtin `True -> true_
        | _, Builtin `False -> not_ a
        | _ -> app_builtin_ arg l
        end
    | (`Ite _ | `Eq _ | `Equiv _), [] -> builtin arg
    | _ -> app_builtin_ arg l

  and not_ t = app_builtin `Not [t]
  and and_ l = app_builtin `And l
  and or_ l = app_builtin `Or l
  and imply a b = app_builtin `Imply [a;b]

  let eq a b = builtin (`Eq (a,b))
  let equiv a b = builtin (`Equiv (a,b))
  let ite a b c = app_builtin (`Ite (a,b,c)) []

  let undefined_ t =
    let id = ID.make "_" in
    builtin (`Undefined (id,t))

  let data_test c t = app_builtin (`DataTest c) [t]
  let data_select c i t = app_builtin (`DataSelect (c,i)) [t]

  let ty_builtin b = T.build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l = if l=[] then f else app f l
  let ty_arrow a b = T.build (TyArrow (a,b))
  let ty_arrow_l args ret = List.fold_right ty_arrow args ret
  let ty_forall v t = T.build (Bind (`TyForall,v,t))
  let ty_var v = T.build (Var v)
  let ty_meta v = T.build (TyMeta v)

  let hash t =
    let d = ref 30 in (* number of nodes to explore *)
    let rec hash_ t h =
      if !d = 0 then h
      else match T.repr t with
        | Const id -> decr d; ID.hash_fun id h
        | Var v -> decr d; hash_var_ v h
        | App (f,l) -> hash_ f h |> CCHash.list hash_ l
        | Builtin b -> CCHash.seq hash_ (Builtin.to_seq b) h
        | Let (v,t,u) -> decr d; hash_var_ v h |> hash_ t |> hash_ u
        | Bind (_,v,t) -> decr d; hash_var_ v h |> hash_ t
        | Match (t,l) ->
            decr d;
            hash_ t h
              |> CCHash.seq
                (fun (vars,rhs) h -> CCHash.list hash_var_ vars h |> hash_ rhs)
                (ID.Map.to_seq l |> Sequence.map snd)
        | TyArrow (a,b) -> decr d; hash_ a h |> hash_ b
        | TyBuiltin _
        | TyMeta _ -> h
      and hash_var_ v h = ID.hash_fun (Var.id v) h
    in
    CCHash.finish (hash_ t CCHash.init)

  module Subst = Var.Subst

  type subst = (T.t, T.t) Subst.t

  let rec equal_with ~subst ty1 ty2 =
    match T.repr ty1, T.repr ty2 with
    | Const id1, Const id2 -> ID.equal id1 id2
    | Var v1, _ when Subst.mem ~subst v1 ->
        equal_with ~subst (Subst.find_exn ~subst v1) ty2
    | _, Var v2 when Subst.mem ~subst v2 ->
        equal_with ~subst ty1 (Subst.find_exn ~subst v2)
    | Var v1, Var v2 -> Var.equal v1 v2
    | Builtin b1, Builtin b2 -> Builtin.equal (equal_with ~subst) b1 b2
    | TyBuiltin b1, TyBuiltin b2 -> TyBuiltin.equal b1 b2
    | TyMeta v1, TyMeta v2 -> MetaVar.equal v1 v2
    | App (f1,l1), App (f2, l2) ->
        equal_with ~subst f1 f2
          && List.length l1 = List.length l2
          && List.for_all2 (equal_with ~subst) l1 l2
    | TyArrow (a1,b1), TyArrow (a2,b2) ->
        equal_with ~subst a1 a2 && equal_with ~subst b1 b2
    | Bind (b1, v1, t1), Bind (b2, v2, t2) ->
        b1 = b2 &&
        ( let v = Var.fresh_copy v1 in
          let subst = Subst.add ~subst v1 (var v) in
          let subst = Subst.add ~subst v2 (var v) in
          equal_with ~subst t1 t2)
    | Let (v1,t1,u1), Let (v2,t2,u2) ->
        let subst = Subst.add ~subst v1 t1 in
        let subst = Subst.add ~subst v2 t2 in
        equal_with ~subst u1 u2
    | Match (t1,l1), Match (t2,l2) ->
        ID.Map.cardinal l1 = ID.Map.cardinal l2 &&
        equal_with ~subst t1 t2 &&
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
            equal_with ~subst rhs1 rhs2
          )
          (cases_to_list l1) (* list, sorted by ID *)
          (cases_to_list l2)
    | Var _, _
    | Match _, _
    | TyBuiltin _,_
    | Builtin _,_
    | Const _,_
    | App (_,_),_
    | Let (_,_,_),_
    | TyArrow (_,_),_
    | Bind _, _
    | TyMeta _,_ -> false

  let equal a b = equal_with ~subst:Subst.empty a b

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
    | Builtin b ->
        builtin (Builtin.map b ~f:(eval ~subst))
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
          if equal_with ~subst a b
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

  let prop = ty_prop
  let prop1 = ty_arrow prop prop
  let prop2 = ty_arrow prop (ty_arrow prop prop)

  let rec ty_exn ~sigma t = match T.repr t with
    | Const id -> find_ty_ ~sigma id
    | Builtin b ->
        begin match b with
          | `Imply -> prop2
          | `Or
          | `And -> assert false (* should be handled below *)
          | `Not -> prop1
          | `True
          | `False -> prop
          | `Ite (_,b,_) -> ty_exn ~sigma b
          | `Equiv (_,_)
          | `Eq (_,_) -> prop
          | `DataTest id ->
              (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
              let ty = find_ty_ ~sigma id in
              ty_arrow (ty_returns ty) prop
          | `DataSelect (id,n) ->
              (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
              let ty = find_ty_ ~sigma id in
              begin match get_ty_arg_ ty n with
              | Some ty_arg ->
                  ty_arrow (ty_returns ty) ty_arg
              | _ ->
                  failwith "cannot infer type, wrong argument to DataSelect"
              end
          | `Undefined (_,t) -> ty_exn ~sigma t
        end
    | Var v -> Var.ty v
    | App (f,l) ->
        begin match T.repr f with
        | Builtin (`And | `Or) -> prop
        | _ -> ty_apply (ty_exn ~sigma f) (List.map (ty_exn ~sigma) l)
        end
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
    with e -> Utils.err_of_exn e

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
      | Builtin b1, Builtin b2 ->
          Builtin.fold2 b1 b2 ~x:subst
            ~fail:(fun () -> error_unif_ "do not match" t1 t2)
            ~f:match_
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
      | Builtin _, _
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
          if equal_with ~subst t1' t2
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

  let rec repr t = match t.view with
    | TyMeta {MetaVar.deref=Some t'; _} -> repr t'
    | v -> v

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
        make_raw_ (App (f, l1 @ l2))
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
      | Builtin b -> Builtin (Builtin.map ~f:convert b)
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
