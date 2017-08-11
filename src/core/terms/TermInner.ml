
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Main View for terms} *)

type id = ID.t
type 'a var = 'a Var.t
type 'a or_error = ('a, string) CCResult.t
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

module TyBuiltin = struct
  type t =
    [ `Kind
    | `Type
    | `Prop
    | `Unitype (** when there is only one type *)
    ]
  let equal = (=)
  let compare = Pervasives.compare
  let to_string = function
    | `Prop -> "prop"
    | `Kind -> "kind"
    | `Type -> "type"
    | `Unitype -> "unitype"
end

type 'a case = 'a var list * 'a
(** A pattern match case for a given constructor [ vars, right-hand side ]
    The pattern must be linear (variable list does not contain duplicates) *)

(** A list of cases (indexed by constructor) *)
type 'a cases = 'a case ID.Map.t

type 'a default_case =
  | Default_none
  | Default_some of 'a * int ID.Map.t
  (* default term, + set of cstors covered this way along with their arity *)

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
  | Match of 'a * 'a cases * 'a default_case (** shallow pattern-match, with default *)
  | TyBuiltin of TyBuiltin.t (** Builtin type *)
  | TyArrow of 'a * 'a  (** Arrow type *)
  | TyMeta of 'a MetaVar.t

(* NOTE: Eq has its own case (in Builtin), because its type parameter is
   often hidden.
   For instance, when we parse a model back from TPTP or SMT, equalities
   are not annotated with their type parameter; we would have to compute or
   infer types again for an unclear benefit (usually just for printing).

   Instead, we just consider equality  to be a specific "ad-hoc polymorphic"
   predicate and do not require it to have a type argument.
*)

type 't repr = 't -> 't view
(** A concrete representation of terms by the type ['t] *)

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
  val pp : t printer
  val pp' : Precedence.t -> t printer
  val pp_in_app : t printer
  val pp_in_binder : t printer
  val to_string : t -> string

  val to_sexp : t -> Sexp_lib.t
end

module Print(T : REPR)
  : PRINT with type t = T.t
= struct
  module P = Precedence

  type t = T.t

  let is_if_ t = match T.repr t with
    | Builtin (`Ite _) -> true
    | _ -> false

  let rec unroll_if_ t = match T.repr t with
    | Builtin (`Ite (a,b,c)) ->
      let l, last = unroll_if_ c in
      (a,b) :: l, last
    | _ -> [], t

  let rec unroll_binder b t = match T.repr t with
    | Bind (b', v, t') when b=b' ->
      let vars, body = unroll_binder b t' in
      v :: vars, body
    | _ -> [], t

  let right_assoc_ = function
    | P.Eq
    | P.Guard
    | P.App
    | P.And
    | P.Or -> false
    | P.Bot
    | P.Top
    | P.Not
    | P.Arrow
    | P.Ite
    | P.Bind -> true

  (* put "()" around [fmt] if needed *)
  let wrap p1 p2 out fmt =
    if p1>p2 || (p1 = p2 && (not (right_assoc_ p1)))
    then (
      CCFormat.string out "(";
      Format.kfprintf (fun _ -> CCFormat.string out ")") out fmt
    )
    else Format.kfprintf (fun _ -> ()) out fmt

  let rec pp' p out t = match T.repr t with
    | TyBuiltin b -> CCFormat.string out (TyBuiltin.to_string b)
    | Const id -> ID.pp out id
    | TyMeta v -> MetaVar.pp out v
    | Var v -> Var.pp_full out v
    | Builtin (`Ite (a,b,c)) when is_if_ c ->
      (* special case to avoid deep nesting of ifs *)
      let pp_middle out (a,b) =
        fpf out "@[<2>else if@ @[%a@]@]@ @[<2>then@ @[%a@]@]"
          (pp' P.Ite) a (pp' P.Ite) b
      in
      let middle, last = unroll_if_ c in
      assert (not (is_if_ last));
      wrap P.Ite p out
        "@[<hv>@[<2>if@ @[%a@]@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
        (pp' P.Ite) a (pp' P.Ite) b
        (Utils.pp_list ~sep:"" pp_middle) middle
        (pp' P.Ite) last
    | Builtin b ->
      let p' = Builtin.prec b in
      wrap p' p out "%a" (Builtin.pp (pp' p')) b
    | App (f,l) ->
      wrap P.App p out "@[<2>%a@ %a@]" pp_in_app f
        (Utils.pp_list ~sep:" " pp_in_app) l
    | Let (v,t,u) ->
      wrap P.Top p out "@[let @[<2>%a :=@ %a@] in@ %a@]"
        Var.pp_full v pp t pp u
    | Match (t,l, def) ->
      let pp_case out (id,(vars,t)) =
        fpf out "@[<hv2>| @[<hv2>%a %a@] ->@ %a@]"
          ID.pp id (Utils.pp_list ~sep:" " Var.pp_full) vars pp t
      and pp_def out = function
        | Default_none -> ()
        | Default_some (d,_) -> fpf out "@ @[<hv2>| default ->@ %a@]" pp d
      in
      fpf out "@[<hv>@[<hv2>match @[%a@] with@ %a%a@]@ end@]"
        pp t (Utils.pp_list ~sep:"" pp_case) (ID.Map.to_list l)
        pp_def def
    | Bind (b, _, _) ->
      let s = Binder.to_string b in
      let vars, body = unroll_binder b t in
      wrap P.Bind p out "@[<2>%s @[<hv>%a@].@ %a@]" s
        (Utils.pp_list ~sep:" " pp_typed_var) vars pp_in_binder body
    | TyArrow (a,b) ->
      (* TODO: left should have [P.Arrow] but ignoring the right-assoc *)
      wrap P.Arrow p out "@[<2>%a ->@ %a@]" (pp' P.App) a (pp' P.Arrow) b
  and pp_typed_var out v =
    let ty = Var.ty v in
    fpf out "(@[%a:@,@[%a@]@])" Var.pp_full v pp ty
  and pp_in_app out t = pp' P.App out t
  and pp_in_binder out t = pp' P.Bind out t
  and pp out t = pp' P.Top out t

  let to_string = CCFormat.to_string pp

  let str = Sexp_lib.atom
  let lst = Sexp_lib.list

  let rec to_sexp t : Sexp_lib.t = match T.repr t with
    | TyBuiltin b -> str (TyBuiltin.to_string b)
    | Const id -> str (ID.name id)
    | TyMeta _ -> assert false
    | Var v -> str (Var.to_string_full v)
    | Builtin b -> Builtin.to_sexp to_sexp b
    | App (f,l) -> lst (to_sexp f :: List.map to_sexp l)
    | Let (v,t,u) ->
      lst [str "let"; lst [lst [var_to_sexp v; to_sexp t]]; to_sexp u]
    | Match (t,l,d) ->
      let last = match d with
        | Default_none -> []
        | Default_some (d,_) -> [lst [str "default"; to_sexp d]]
      in
      lst
        (str "match" ::
           to_sexp t ::
           ID.Map.fold
             (fun c (vars,t) acc ->
                lst [str (ID.to_string c); lst (List.map var_to_sexp vars); to_sexp t]
                :: acc)
             l last)
    | Bind (b, _, _) ->
      let s = Binder.to_string b in
      let vars, body = unroll_binder b t in
      lst [str s; lst (List.map var_to_sexp vars); to_sexp body]
    | TyArrow (a,b) ->
      lst [str "->"; to_sexp a; to_sexp b]
  and var_to_sexp v =
    lst [str (Var.to_string_full v); to_sexp (Var.ty v)]
end

type 'a print = (module PRINT with type t = 'a)

(** {2 Utils} *)

module type UTIL_REPR = sig
  type t_

  val head_sym : t_ -> id option
  (** Search for a head symbol, if any *)

  exception No_head of t_

  val head_sym_exn : t_ -> id
  (** Search for a head symbol
      @raise No_head if not an application/const *)

  val to_seq : t_ -> t_ Sequence.t
  (** Iterate on sub-terms *)

  val to_seq_vars : t_ -> t_ Var.t Sequence.t
  (** Iterate on variables *)

  val to_seq_consts : t_ -> ID.t Sequence.t
  (** IDs occurring as {!Const} *)

  module VarSet : CCSet.S with type elt = t_ Var.t

  val to_seq_free_vars : ?bound:VarSet.t -> t_ -> t_ Var.t Sequence.t
  (** Iterate on free variables. *)

  val free_vars : ?bound:VarSet.t -> t_ -> VarSet.t
  (** [free_vars t] computes the set of free variables of [t].
      @param bound variables bound on the path *)

  val free_vars_seq : ?bound:VarSet.t -> t_ Sequence.t -> VarSet.t
  (** Similar to {!free_vars} but for a sequence of terms *)

  val free_vars_list : ?bound:VarSet.t -> t_ list -> VarSet.t

  val is_var : t_ -> bool
  val is_const : t_ -> bool

  val is_closed : t_ -> bool
  (** [is_closed t] means [to_seq_free_vars t = empty] *)

  val is_undefined : t_ -> bool

  val free_meta_vars : ?init:t_ MetaVar.t ID.Map.t -> t_ -> t_ MetaVar.t ID.Map.t
  (** The free type meta-variables in [t] *)

  val bind_unfold : Binder.t -> t_ -> t_ Var.t list * t_
  (** [bind_unfold binder (bind binder x1...xn. t)] returns [x1...xn, t] *)

  val fun_unfold : t_ -> t_ Var.t list * t_
  (** [fun_unfold (fun x y z. t) = [x;y;z], t].
      Special case of {!bind_unfold} *)

  val get_ty_arg : t_ -> int -> t_ option
  (** [get_ty_arg ty n] gets the [n]-th argument of [ty], if [ty] is a
      function type with at least [n] arguments. *)

  val ty_unfold : t_ -> t_ Var.t list * t_ list * t_
  (** [ty_unfold ty] decomposes [ty] into a list of quantified type variables,
      a list of parameters, and a return type (which is not an arrow).

      [ty_unfold (forall a b, a -> b -> c -> d)] will return
      [([a;b], [a;b;c], d)]
  *)

  val app_const_unfold : t_ -> (ID.t * t_ list) option
  (** [app_const_unfold (app_const id l)] returns [Some (id,l)];
      [app_const_unfold (const id)] returns [Some (id, [])];
      otherwise it returns [None] *)

  val ite_unfold : t_ -> (t_ * t_) list * t_
  (** [ite_unfold (if a b (if a' b' … e))] returns [[(a,b);(a',b')…],e],
      i.e. a series of "if/then" and a final "else" *)

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

  val ty_is_unitype : t_ -> bool

  val ty_arity : t_ -> int
  (** If type is a function [forall v1...vk. a1 -> ... -> an -> ret],
      returns [k+n]. Returns [0] otherwise.
      In other words, this returns the maximal number of arguments
      anything with this type can be applied to. *)

  val ty_num_param : t_ -> int
  (** Number of type arguments that any value of this type accepts.

      NOTE: this is not simply [ty_unfold], because some nameless parameters
      might still be of type "ty".

      For instance, returns 2 on the type
      [pi a:type. type -> foo -> bar],
      because any value with this type should be applied to 2 type parameters. *)
end

let iter_default_case f = function
  | Default_none ->  ()
  | Default_some (t, _) -> f t

let map_default_case f = function
  | Default_none -> Default_none
  | Default_some (t, ids) -> Default_some (f t, ids)

let map_default_case' f = function
  | Default_none -> Default_none
  | Default_some (t, ids) ->
    let t, ids = f t ids in
    Default_some (t, ids)

(** Utils that only require a {!REPR} *)
module UtilRepr(T : REPR)
  : UTIL_REPR with type t_ = T.t
= struct
  type t_ = T.t

  exception No_head of t_

  let () = Printexc.register_printer
      (function
        | No_head t ->
          let module P = Print(T) in
          Some (CCFormat.sprintf "term `@[%a@]` has no head" P.pp t)
        | _ -> None)

  let head_sym_exn t =
    let rec aux u = match T.repr u with
      | App (f, _) -> aux f
      | Const id -> id
      | _ -> raise (No_head t)
    in aux t

  let head_sym t =
    try Some (head_sym_exn t)
    with No_head _ -> None

  let to_seq t yield =
    let rec aux t =
      yield t;
      match T.repr t with
        | TyMeta _ -> ()
        | TyBuiltin _
        | Const _ -> ()
        | Var v -> aux_var v
        | Match (t,l,d) ->
          aux t;
          ID.Map.iter (fun _ (vars,rhs) -> List.iter aux_var vars; aux rhs) l;
          iter_default_case aux d;
        | Builtin b -> Builtin.iter aux b
        | App (f,l) -> aux f; List.iter aux l
        | Bind (_,v,t) -> aux_var v; aux t
        | Let (v,t,u) -> aux_var v; aux t; aux u
        | TyArrow (a,b) -> aux a; aux b
    and aux_var v = aux (Var.ty v)
    in
    aux t

  module VarSet = Var.Set(T)

  let to_seq_free_vars ?(bound=VarSet.empty) t yield =
    let rec aux ~bound t = match T.repr t with
      | Const _ -> ()
      | Var v ->
        if VarSet.mem v bound then () else yield v;
        aux ~bound (Var.ty v)
      | App (f,l) ->
        aux ~bound f; List.iter (aux ~bound) l
      | Match (t,l,d) ->
        aux ~bound t;
        ID.Map.iter
          (fun _ (vars,rhs) ->
             List.iter (fun v -> aux ~bound (Var.ty v)) vars;
             let bound = List.fold_right VarSet.add vars bound in
             aux ~bound rhs)
          l;
        iter_default_case (aux ~bound) d;
      | Builtin b -> Builtin.iter (aux ~bound) b
      | Bind (_,v,t) ->
        aux ~bound (Var.ty v); aux ~bound:(VarSet.add v bound) t
      | Let (v,t,u) ->
        aux ~bound (Var.ty v); aux ~bound t; aux ~bound:(VarSet.add v bound) u
      | TyBuiltin _ -> ()
      | TyArrow (a,b) -> aux ~bound a; aux ~bound b
      | TyMeta _ -> ()
    in
    aux ~bound t

  let to_seq_consts t =
    to_seq t
    |> Sequence.filter_map
      (fun t -> match T.repr t with
         | Const id -> Some id
         | _ -> None)

  let free_vars ?bound t =
    to_seq_free_vars ?bound t |> VarSet.of_seq

  let free_vars_seq ?bound seq =
    seq |> Sequence.flat_map (to_seq_free_vars ?bound) |> VarSet.of_seq

  let free_vars_list ?bound l = free_vars_seq ?bound (Sequence.of_list l)

  let is_var t = match T.repr t with Var _ -> true | _ -> false
  let is_const t = match T.repr t with Const _ -> true | _ -> false

  let is_closed t = to_seq_free_vars t |> Sequence.is_empty

  let is_undefined t = match T.repr t with Builtin (`Undefined_self _) -> true | _ -> false

  let to_seq_vars t =
    to_seq t
    |> Sequence.flat_map
      (fun t -> match T.repr t with
         | Var v
         | Bind (_,v,_)
         | Let (v,_,_) -> Sequence.return v
         | Match (_,l,_) ->
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

  let bind_unfold b t =
    let rec aux vars t = match T.repr t with
      | Bind (b', v, t') when b=b' -> aux (v::vars) t'
      | _ -> List.rev vars, t
    in
    aux [] t

  let fun_unfold t = bind_unfold Binder.Fun t

  let ty_unfold t =
    let rec aux1 t = match T.repr t with
      | TyArrow (l, r) ->
        let args, ret = aux2 r in
        [], l :: args, ret
      | Bind (Binder.TyForall, v, t') ->
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

  let app_const_unfold t = match T.repr t with
    | Const id -> Some (id, [])
    | App (f, l) ->
      begin match T.repr f with
        | Const id -> Some (id, l)
        | _ -> None
      end
    | _ -> None

  let ite_unfold t =
    let rec aux l t = match T.repr t with
      | Builtin (`Ite (a,b,c)) ->
        aux ((a,b)::l) c
      | _ -> List.rev l, t
    in
    aux [] t

  let ty_is_Type t = match T.repr t with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_is_Kind t = match T.repr t with
    | TyBuiltin `Kind -> true
    | _ -> false

  let ty_is_Prop t = match T.repr t with
    | TyBuiltin `Prop -> true
    | _ -> false

  let ty_is_unitype t = match T.repr t with
    | TyBuiltin `Unitype -> true
    | _ -> false

  let rec ty_returns t = match T.repr t with
    | TyArrow (_, t') -> ty_returns t'
    | Bind (Binder.TyForall, _, t') -> ty_returns t'
    | _ -> t

  let ty_returns_Type t = match T.repr (ty_returns t) with
    | TyBuiltin `Type -> true
    | _ -> false

  let ty_returns_Prop t = match T.repr (ty_returns t) with
    | TyBuiltin `Prop -> true
    | _ -> false

  let rec get_ty_arg ty i = match T.repr ty with
    | App (_,_)
    | TyBuiltin _
    | Const _
    | Var _
    | TyMeta _ -> None
    | TyArrow (a,b) ->
      if i=0 then Some a else get_ty_arg b (i-1)
    | Bind (Binder.TyForall, _,_) -> None
    | _ -> assert false

  (* number of parameters of this (polymorphic?) T.t type. *)
  let rec ty_num_param ty = match T.repr ty with
    | TyMeta _ | Var _ | Const _ | App _ | TyBuiltin _ -> 0
    | TyArrow (a,t') ->
      if ty_is_Type a
      then 1 + ty_num_param t' (* [a] is a type parameter *)
      else 0 (* asks for term parameters *)
    | Bind (Binder.TyForall, _,t) -> 1 + ty_num_param t
    | _ -> assert false

  let ty_arity ty =
    let vars, args, _ = ty_unfold ty in
    List.length vars + List.length args
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

  val build : t_ view -> t_
  val const : id -> t_
  val builtin : t_ Builtin.t -> t_
  val app_builtin : t_ Builtin.t -> t_ list -> t_
  val var : t_ var -> t_
  val app : t_ -> t_ list -> t_
  val app_const : ID.t -> t_ list -> t_
  val fun_ : t_ var -> t_ -> t_
  val mu : t_ var -> t_ -> t_
  val let_ : t_ var -> t_ -> t_ -> t_
  val match_with : t_ -> t_ cases -> def:t_ default_case -> t_
  val ite : t_ -> t_ -> t_ -> t_
  val forall : t_ var -> t_ -> t_
  val exists : t_ var -> t_ -> t_

  val eq : t_ -> t_ -> t_
  val neq : t_ -> t_ -> t_
  val imply : t_ -> t_ -> t_
  val imply_l : t_ list -> t_ -> t_
  val true_ : t_
  val false_ : t_
  val and_ : t_ list -> t_
  val or_ : t_ list -> t_
  val not_ : t_ -> t_
  val undefined_self : t_ -> t_ (** fresh undefined term *)
  val undefined_atom : ty:t_ -> t_ (** fresh undefined constant *)
  val data_test : ID.t -> t_ -> t_
  val data_select : ID.t -> int -> t_ -> t_
  val unparsable : ty:t_ -> t_

  (** No simplifications *)
  module No_simp : sig
    val builtin : t_ Builtin.t -> t_
    val app_builtin : t_ Builtin.t -> t_ list -> t_

    val eq : t_ -> t_ -> t_
    val neq : t_ -> t_ -> t_
    val imply : t_ -> t_ -> t_
    val imply_l : t_ list -> t_ -> t_
    val and_ : t_ list -> t_
    val or_ : t_ list -> t_
    val not_ : t_ -> t_
    val ite : t_ -> t_ -> t_ -> t_
  end

  val and_nodup : t_ list -> t_

  val asserting : t_ -> t_ list -> t_
  val guard : t_ -> t_ Builtin.guard -> t_

  val mk_bind : Binder.t -> t_ var -> t_ -> t_
  val mk_bind_l : Binder.t -> t_ var list -> t_ -> t_

  val ty_type : t_ (** Type of types *)
  val ty_kind : t_ (** Type of ty_type *)
  val ty_prop : t_ (** Propositions *)
  val ty_unitype : t_

  val ty_builtin : TyBuiltin.t -> t_
  val ty_const : id -> t_
  val ty_app : t_ -> t_ list -> t_
  val ty_arrow : t_ -> t_ -> t_
  val ty_arrow_l : t_ list -> t_ -> t_
  val ty_var : t_ var -> t_
  val ty_meta : t_ MetaVar.t -> t_
  val ty_forall : t_ var -> t_ -> t_

  val fun_l : t_ var list -> t_ -> t_
  val forall_l : t_ var list -> t_ -> t_
  val exists_l : t_ var list -> t_ -> t_
  val ty_forall_l : t_ var list -> t_ -> t_
  val let_l : (t_ var * t_) list -> t_ -> t_

  val close_forall : t_ -> t_
  (** [close_forall t] universally quantifies over free variables of [t] *)

  val hash : t_ -> int
  (** Hash into a positive integer *)

  val hash_alpha_eq : t_ -> int
  (** Hash function that is not sensitive to alpha-renaming *)

  val equal : t_ -> t_ -> bool
  (** Syntactic equality *)

  (** {2 Misc} *)

  module Tbl : CCHashtbl.S with type key = t_
  (** Hashtbl with terms as key. The hash function is modulo α-equiv *)

  module Map : CCMap.S with type key = t_
  (** Map with terms as key. The hash function is modulo α-equiv *)

  val remove_dup : t_ list -> t_ list
  (** Use a hashset to remove duplicates from the list. Order is
      not preserved. *)

  (** {6 Traversal} *)

  val fold :
    f:('acc -> 'b_acc -> t_ -> 'acc) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc) ->
    'acc ->
    'b_acc ->
    t_ ->
    'acc
  (** Non recursive fold.
      @param bind updates the binding accumulator with the bound variable
      @param f used to update the regular accumulator (that is returned) *)

  val iter :
    f:('b_acc -> t_ -> unit) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc) ->
    'b_acc ->
    t_ ->
    unit
  (** Non recursive iter.
      @param bind updates the binding accumulator with the bound variable
      @param f called on immediate subterms and on the regular accumulator *)

  val map_generic :
    f:('b_acc -> t_ -> 'a) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * 'a Var.t) ->
    'b_acc ->
    t_ ->
    'a view
  (** Non recursive polymorphic map, returning a new view. Combine with
        {!T.build} in the special case of terms.
      @param f maps a term to a term
      @param bind updates the binding accumulator and returns a new variable *)

  val map :
    f:('b_acc -> t_ -> t_) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * t_ Var.t) ->
    'b_acc -> t_ -> t_
  (** Special version of {!map_generic} for terms *)

  val map_pol :
    f:('b_acc -> Polarity.t -> t_ -> t_) ->
    bind:('b_acc -> t_ Var.t -> 'b_acc * t_ Var.t) ->
    'b_acc ->
    Polarity.t ->
    t_ ->
    t_
  (** Similar to {!map} but also keeping the subterm polarity *)

  val approx_infinite_quant_pol :
    [`Forall|`Exists|`Eq] ->
    Polarity.t ->
    [`Unsat_means_unknown of t_ | `Keep]
  (** Approximation of [q] under the polarity [pol]: either

      - [`Unsat_means_unknown replacement] means that we lost completeness,
          and should return [replacement] instead
      - [`Keep] means to keep the quantifier as is *)

  val approx_infinite_quant_pol_binder :
    Binder.t ->
    Polarity.t ->
    [`Unsat_means_unknown of t_ | `Keep]
  (** Version of {!approx_infinite_quant_pol} that takes a binder.
      @raise Assert_failure on everything but Forall and Exists *)

  val size : t_ -> int
  (** Number of AST nodes *)

  (** {6 Substitution Utils} *)

  type subst = (t_, t_) Var.Subst.t
  type renaming = (t_, t_ Var.t) Var.Subst.t

  val equal_with : subst:subst -> t_ -> t_ -> bool
  (** Equality modulo substitution *)

  val deref : subst:subst -> t_ -> t_
  (** [deref ~subst t] dereferences [t] as long as it is a variable
      bound in [subst]. *)

  val rename_var : subst -> t_ Var.t -> subst * t_ Var.t
  (** Same as {!Subst.rename_var} but wraps the renamed var in a term *)

  type apply_error = {
    ae_msg: string;
    ae_term: t_ option;
    ae_ty: t_;
    ae_args: t_ list;
    ae_args_ty: t_ list; (* same length as ae_args *)
    ae_subst: subst;
  }

  exception ApplyError of apply_error
  (** Raised when a type application fails *)

  val eval : ?rec_:bool -> subst:subst -> t_ -> t_
  (** Applying a substitution
      @param rec_ if true, when replacing [v] with [t]
        because [(v -> t) in subst], we call [eval subst t] instead of
        assuming [t] is preserved by subst (default false) *)

  val eval_renaming : subst:renaming -> t_ -> t_
  (** Applying a variable renaming *)

  val renaming_to_subst : renaming -> subst

  val ty_apply : t_ -> terms:t_ list -> tys:t_ list -> t_
  (** [apply t ~terms ~tys] computes the type of [f terms] for some
      function [f], where [f : t] and [terms : ty].
      @raise ApplyError if the arguments do not match *)

  val ty_apply_full : t_ -> terms:t_ list -> tys:t_ list -> t_ * subst
  (** [ty_apply_full ty l] is like [apply t l], but it returns a pair
      [ty' , subst] such that [subst ty' = apply t l].
      @raise ApplyError if the arguments do not match *)

  val ty_apply_mono : t_ -> tys:t_ list -> t_
  (** [apply t ~tys] computes the type of [f terms] for some
      function [f], where [f : t] and [terms : ty].
      @raise Invalid_argument if [t] is not monomorphic (i.e. not TyForall)
      @raise ApplyError if the arguments do not match *)

  type signature = id -> t_ option
  (** A signature is a way to obtain the type of a variable *)

  val ty_of_signature : sigma:signature -> t_ -> t_ or_error
  (** Compute the type of the given term in the given signature. *)

  val ty_of_signature_exn : sigma:signature -> t_ -> t_

  val ty : env:(t_,t_) Env.t -> t_ -> t_ or_error
  (** Compute type of this term in this environment *)

  val ty_exn : env:(t_,t_) Env.t -> t_ -> t_
  (** Same as {!ty} but unsafe.
      @raise Failure in case of error at an application
      @raise Env.Undefined in case some symbol is not defined *)

  val info_of_ty : env:(t_,t_) Env.t -> t_ -> (t_, t_) Env.info or_error
  (** [info_of_ty ~env ty] finds the information related to the given
      type in the given environment. *)

  val info_of_ty_exn : env:(t_,t_) Env.t -> t_ -> (t_, t_) Env.info
  (** Unsafe version of {!info_of_ty}
      @raise No_head if the type is not an (applied) constant *)

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
  let ty_unitype = T.build (TyBuiltin `Unitype)

  let build = T.build
  let const id = T.build (Const id)
  let var v = T.build (Var v)
  let app t l = match l with
    | [] -> t
    | _::_ -> T.build (App(t,l))
  let app_const id l = app (const id) l
  let mk_bind b v t = T.build (Bind (b, v, t))
  let mk_bind_l b = List.fold_right (mk_bind b)
  let fun_ v t = T.build (Bind (Binder.Fun, v, t))
  let mu v t = T.build (Bind (Binder.Mu, v, t))

  let let_ v t u = match T.repr u with
    | Builtin `True
    | Builtin `False -> u
    | _ -> T.build (Let (v, t, u))

  let match_with t m ~def =
    begin match def with
      | Default_none when ID.Map.is_empty m ->
        invalid_arg "Term.case: empty list of cases";
      | Default_some (d,_) when ID.Map.is_empty m -> d
      | _ ->
        T.build (Match (t,m,def))
    end

  let forall v t = match T.repr t with
    | Builtin `True
    | Builtin `False -> t
    | _ -> T.build (Bind(Binder.Forall,v, t))

  let exists v t = match T.repr t with
    | Builtin `True
    | Builtin `False -> t
    | _ -> T.build (Bind(Binder.Exists,v, t))

  exception FlattenExit of T.t

  let flatten (b:[<`And | `Or]) l =
    try
      CCList.flat_map
        (fun t -> match T.repr t with
           | Builtin `True when b=`And -> []
           | Builtin `True when b=`Or -> raise (FlattenExit t) (* shortcut *)
           | Builtin `False when b=`Or -> []
           | Builtin `False when b=`And -> raise (FlattenExit t)
           | Builtin (`And l') when b=`And -> l'
           | Builtin (`Or l') when b=`Or -> l'
           | _ -> [t])
        l
    with FlattenExit t ->
      [t]

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
        | _, Builtin `True, _ -> or_ [a; c] (* then branch: true *)
        | _, Builtin `False, _ -> and_ [not_ a; c] (* then branch: false *)
        | _, _, Builtin `True -> imply a b (* else branch: true *)
        | _, _, Builtin `False -> and_ [a; b] (* else branch: false *)
        | _ -> builtin_ arg
      end
    | `Eq (a,b) ->
      begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | _, Builtin `True -> a
        | Builtin `False, _ -> not_ b
        | _, Builtin `False -> not_ a
        | _ -> builtin_ arg
      end
    | `And l ->
      begin match flatten `And l with
        | [] -> true_
        | [x] -> x
        | l -> builtin_ (`And l)
      end
    | `Or l ->
      begin match flatten `Or l with
        | [] -> false_
        | [x] -> x
        | l -> builtin_ (`Or l)
      end
    | `Not t ->
      begin match T.repr t with
        | Builtin `True -> false_
        | Builtin `False -> true_
        | Builtin (`And l) -> or_ (List.map not_ l)
        | Builtin (`Or l) -> and_ (List.map not_ l)
        | Builtin (`Not t) -> t
        | _ -> builtin_ (`Not t)
      end
    | `Imply (a,b) ->
      begin match T.repr a, T.repr b with
        | Builtin `True, _ -> b
        | Builtin `False, _ -> true_
        | _, Builtin `True -> true_
        | _, Builtin `False -> not_ a
        | _ -> builtin_ (`Imply (a,b))
      end
    | _ -> builtin_ arg

  and app_builtin arg l = match arg, l with
    | (`Ite _ | `Eq _), [] -> builtin arg
    | _ -> app_builtin_ arg l

  and not_ t = builtin (`Not t)
  and and_ l = builtin (`And l)
  and or_ l = builtin (`Or l)
  and imply a b = builtin (`Imply (a,b))

  let imply_l l ret = match l with
    | [] -> ret
    | [a] -> imply a ret
    | _ -> imply (and_ l) ret

  let eq a b = builtin (`Eq (a,b))
  let neq a b = not_ (eq a b)
  let ite a b c = app_builtin (`Ite (a,b,c)) []

  let undefined_self t = builtin (`Undefined_self t)

  let undefined_atom ~ty =
    let id = ID.make "_" in
    builtin (`Undefined_atom (id,ty))

  let data_test c t = app_builtin (`DataTest c) [t]
  let data_select c i t = app_builtin (`DataSelect (c,i)) [t]
  let unparsable ~ty = builtin (`Unparsable ty)

  let guard t g =
    let open Builtin in
    match T.repr t, g.asserting with
      | _, [] -> t
      | Builtin (`Guard (t', g')), _ ->
        let g'' = Builtin.merge_guard g g' in
        builtin (`Guard (t', g''))
      | _ ->
        builtin (`Guard (t, g))

  let asserting t p = guard t {Builtin.asserting=p}

  module No_simp = struct
    let builtin b = T.build (Builtin b)
    let app_builtin b l = app (builtin b) l

    let not_ t = builtin (`Not t)
    let and_ l = builtin (`And l)
    let or_ l = builtin (`Or l)
    let imply a b = builtin (`Imply (a,b))

    let imply_l l ret = match l with
      | [] -> ret
      | [a] -> imply a ret
      | _ -> imply (and_ l) ret

    let eq a b = builtin (`Eq (a,b))
    let neq a b = not_ (eq a b)
    let ite a b c = app_builtin (`Ite (a,b,c)) []
  end

  let ty_builtin b = T.build (TyBuiltin b)
  let ty_const id = const id
  let ty_app f l = if l=[] then f else app f l
  let ty_arrow a b = T.build (TyArrow (a,b))
  let ty_arrow_l args ret = List.fold_right ty_arrow args ret
  let ty_forall v t = T.build (Bind (Binder.TyForall,v,t))
  let ty_var v = T.build (Var v)
  let ty_meta v = T.build (TyMeta v)

  let fun_l = List.fold_right fun_
  let forall_l = List.fold_right forall
  let exists_l = List.fold_right exists
  let ty_forall_l = List.fold_right ty_forall
  let let_l l = List.fold_right (fun (v,t) u -> let_ v t u) l

  let close_forall t =
    let fvars = free_vars t |> VarSet.to_list in
    forall_l fvars t

  let hash_ hash_var t =
    let d = ref 30 in (* number of nodes to explore *)
    let rec hash_ t =
      if !d = 0 then 0x42
      else match T.repr t with
        | Const id -> decr d; ID.hash id
        | Var v -> decr d; hash_var v
        | App (f,l) -> CCHash.combine3 20 (hash_ f) (CCHash.list hash_ l)
        | Builtin b -> CCHash.combine2 30 (CCHash.seq hash_ (Builtin.to_seq b))
        | Let (v,t,u) -> decr d; CCHash.combine4 40 (hash_var v) (hash_ t) (hash_ u)
        | Bind (_,v,t) -> decr d; CCHash.combine3 50 (hash_var v) (hash_ t)
        | Match (t,l,def) ->
          decr d;
          CCHash.combine4 60
            (hash_ t)
            CCHash.(seq (pair (list hash_var) hash_) 
                (ID.Map.to_seq l |> Sequence.map snd))
            (match def with
              | Default_none -> 0x10
              | Default_some (t,_) -> hash_ t)
        | TyArrow (a,b) -> decr d; CCHash.combine3 70 (hash_ a) (hash_ b)
        | TyBuiltin _
        | TyMeta _ -> 80
    in
    hash_ t

  let hash t =
    let hash_var_ v = ID.hash (Var.id v) in
    hash_ hash_var_ t

  let hash_alpha_eq t =
    let hash_var_ _ = CCHash.string "var" in
    hash_ hash_var_ t

  module Subst = Var.Subst

  type subst = (T.t, T.t) Subst.t
  type renaming = (t_, t_ Var.t) Var.Subst.t

  let rename_var subst v =
    let v' = Var.fresh_copy v in
    Subst.add ~subst v (var v'), v'

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
      | Match (t1,l1,d1), Match (t2,l2,d2) ->
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
        &&
        begin match d1, d2 with
          | Default_none, Default_none -> true
          | Default_some (t1,_), Default_some (t2,_) -> equal_with ~subst t1 t2
          | Default_none, _ | Default_some _, _ -> false
        end
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

  module As_key = struct
    type t = t_
    let compare = compare
    let equal = equal
    let hash = hash_alpha_eq
  end

  module Tbl = CCHashtbl.Make(As_key)
  module Map = CCMap.Make(As_key)

  (* remove duplicates in [l] *)
  let remove_dup l : t_ list =
    match l with
      | []
      | [_] -> l
      | [t1;t2] -> if equal t1 t2 then [t1] else l
      | _ ->
        let h = Tbl.create 16 in
        List.iter (fun t -> Tbl.replace h t ()) l;
        Tbl.keys_list h

  let and_nodup l =
    flatten `And l
    |> remove_dup
    |> and_

  let fold ~f ~bind acc b_acc t =
    let rec fold_l ~f ~bind acc b_acc = function
      | [] -> acc
      | t :: l' ->
        let acc = f acc b_acc t in
        fold_l ~f ~bind acc b_acc l'
    in
    match T.repr t with
      | TyMeta _
      | Const _
      | TyBuiltin _
      | Var _ -> acc
      | App (hd,l) ->
        let acc = f acc b_acc hd in
        fold_l ~f ~bind acc b_acc l
      | Builtin b -> Builtin.fold ~f:(fun acc t -> f acc b_acc t) ~x:acc b
      | Bind (_,v,t) ->
        let b_acc = bind b_acc v in
        f acc b_acc t
      | Let (v,t,u) ->
        let acc = f acc b_acc t in
        let b_acc = bind b_acc v in
        f acc b_acc u
      | Match (t,cases,def) ->
        let acc = f acc b_acc t in
        let acc = match def with
          | Default_none -> acc
          | Default_some (t, _) -> f acc b_acc t
        in
        ID.Map.fold
          (fun _ (vars,rhs) acc ->
             let b_acc = List.fold_left bind b_acc vars in
             f acc b_acc rhs)
          cases acc
      | TyArrow (a,b) ->
        let acc = f acc b_acc a in
        f acc b_acc b

  let iter ~f ~bind b_acc t =
    fold () b_acc t ~bind ~f:(fun () b_acc t -> f b_acc t)

  let map_generic ~f ~bind b_acc t = match T.repr t with
    | TyBuiltin b -> TyBuiltin b
    | Const id -> Const id
    | TyMeta v -> TyMeta (MetaVar.update ~f:(f b_acc) v)
    | Var v -> Var (Var.update_ty ~f:(f b_acc) v)
    | App (hd,l) ->
      let hd = f b_acc hd in
      let l = List.map (f b_acc) l in
      App (hd, l)
    | Builtin b ->
      let b = Builtin.map ~f:(f b_acc) b in
      Builtin b
    | Let (v,t,u) ->
      let t = f b_acc t in
      let b_acc, v' = bind b_acc v in
      let u = f b_acc u in
      Let (v', t, u)
    | Bind (b,v,t) ->
      let b_acc, v' = bind b_acc v in
      let t = f b_acc t in
      Bind (b, v', t)
    | Match (lhs,cases,def) ->
      let lhs = f b_acc lhs in
      let def = map_default_case (f b_acc) def in
      let cases = ID.Map.map
          (fun (vars,rhs) ->
             let b_acc, vars' = Utils.fold_map bind b_acc vars in
             vars', f b_acc rhs)
          cases
      in
      Match (lhs, cases, def)
    | TyArrow (a,b) ->
      let a = f b_acc a in
      let b = f b_acc b in
      TyArrow (a,b)

  let map ~f ~bind b_acc t = T.build (map_generic ~f ~bind b_acc t)

  module P = Polarity

  let map_pol ~f ~bind b_acc pol t = match T.repr t with
    | TyBuiltin _
    | Const _
    | TyMeta _ -> t
    | Var v -> var (Var.update_ty ~f:(f b_acc P.NoPol) v)
    | App (hd,l) ->
      begin match T.repr hd, l with
        | Builtin (`DataTest _ | `DataSelect _), [t] ->
          let hd = f b_acc pol hd in
          let t = f b_acc pol t in
          app hd [t]
        | _ ->
          let hd = f b_acc pol hd in
          let l = List.map (f b_acc P.NoPol) l in
          app hd l
      end
    | Builtin (`Unparsable t) -> unparsable ~ty:(f b_acc (P.NoPol) t)
    | Builtin (`Not t) ->
      let t = f b_acc (P.inv pol) t in
      not_ t
    | Builtin (`Or l) ->
      let l = List.map (f b_acc pol) l in
      or_ l
    | Builtin (`And l) ->
      let l = List.map (f b_acc pol) l in
      and_ l
    | Builtin (`Imply (a,b)) ->
      let a = f b_acc (P.inv pol) a in
      let b = f b_acc pol b in
      imply a b
    | Builtin (`True | `False | `DataSelect _ | `DataTest _) ->
      (* partially applied, or constant *)
      t
    | Builtin (`Undefined_self t) ->
      builtin (`Undefined_self (f b_acc P.NoPol t))
    | Builtin (`Undefined_atom (id,t)) ->
      builtin (`Undefined_atom (id, f b_acc P.NoPol t))
    | Builtin (`Guard (t, g)) ->
      let t = f b_acc pol t in
      let g = Builtin.map_guard (f b_acc Polarity.Pos) g in
      guard t g
    | Builtin (`Eq (a,b)) ->
      let a = f b_acc P.NoPol a in
      let b = f b_acc P.NoPol b in
      eq a b
    | Builtin (`Ite (a,b,c)) ->
      let a = f b_acc P.NoPol a in
      let b = f b_acc pol b in
      let c = f b_acc pol c in
      ite a b c
    | Let (v,t,u) ->
      let t = f b_acc P.NoPol t in
      let b_acc, v' = bind b_acc v in
      let u = f b_acc pol u in
      let_ v' t u
    | Bind ((Binder.Forall | Binder.Exists as b), v, t) ->
      let b_acc, v' = bind b_acc v in
      let t = f b_acc pol t in
      mk_bind b v' t
    | Bind ((Binder.TyForall | Binder.Fun | Binder.Mu) as b, v, t) ->
      (* no polarity in those binders *)
      let b_acc, v' = bind b_acc v in
      let t = f b_acc P.NoPol t in
      mk_bind b v' t
    | Match (lhs,cases,def) ->
      let lhs = f b_acc P.NoPol lhs in
      let def = map_default_case (f b_acc pol) def in
      let cases = ID.Map.map
          (fun (vars,rhs) ->
             let b_acc, vars' = Utils.fold_map bind b_acc vars in
             vars', f b_acc pol rhs)
          cases
      in
      match_with lhs cases ~def
    | TyArrow (a,b) ->
      let a = f b_acc pol a in
      let b = f b_acc pol b in
      ty_arrow a b

  let approx_infinite_quant_pol
      (q:[`Forall|`Exists|`Eq])
      (pol:Polarity.t)
    : [>`Unsat_means_unknown of t_ | `Keep] =
    match q, pol with
      | `Forall, P.Neg
      | `Eq, P.Neg
      | `Exists, P.Pos -> `Keep
      | `Forall, P.Pos
      | `Eq, P.Pos
      | `Exists, P.Neg ->
        let res = if pol=P.Pos then false_ else true_ in
        `Unsat_means_unknown res
      | _, P.NoPol ->
        (* aww. no idea, just avoid this branch if possible *)
        let res = asserting false_ [false_] in
        `Unsat_means_unknown res

  let approx_infinite_quant_pol_binder q pol = match q with
    | Binder.Forall -> approx_infinite_quant_pol `Forall pol
    | Binder.Exists -> approx_infinite_quant_pol `Exists pol
    | _ -> assert false

  let size t =
    let n = ref 0 in
    let rec aux t =
      incr n;
      iter () t ~bind:(fun () _ -> ()) ~f:(fun () t' -> aux t')
    in
    aux t;
    !n

  let rec deref ~subst t = match T.repr t with
    | Var v ->
      begin match Subst.find ~subst v with
        | None -> t
        | Some t' -> deref ~subst t'
      end
    | _ -> t

  let eval ?(rec_=false) ~subst t =
    let rec aux subst t = match T.repr t with
      | Var v ->
        (* NOTE: when dependent types are added, substitution in types
           will be needed *)
        begin match Subst.find ~subst v with
          | None -> t
          | Some t' when rec_ -> aux subst t'
          | Some t' -> t'
        end
      | _ ->
        map subst t
          ~f:aux
          ~bind:(fun subst v ->
            assert (not (Var.Subst.mem ~subst v));
            let v' = Var.fresh_copy v in
            Var.Subst.add ~subst v (var v'), v')
    in
    if Subst.is_empty subst then t else aux subst t

  let eval_renaming ~subst t =
    let rec aux subst t = match T.repr t with
      | Var v ->
        let v' = Subst.deref_rec ~subst v in
        var v'
      | _ ->
        map subst t
          ~f:aux
          ~bind:(fun subst v ->
            assert (not (Var.Subst.mem ~subst v));
            let v' = Var.fresh_copy v in
            Var.Subst.add ~subst v v', v')
    in
    if Subst.is_empty subst then t else aux subst t

  let renaming_to_subst subst = Var.Subst.map ~f:var subst

  type apply_error = {
    ae_msg: string;
    ae_term: t_ option;
    ae_ty: t_;
    ae_args: t_ list;
    ae_args_ty: t_ list; (* same length as ae_args *)
    ae_subst: subst;
  }

  exception ApplyError of apply_error
  (** Raised when a type application fails *)

  exception UnifError of string * T.t * T.t
  (** Raised for unification or matching errors *)

  let () =
    Printexc.register_printer
      (function
        | ApplyError ae ->
          let module P = Print(T) in
          let pp_t out = function
            | None -> ()
            | Some t -> fpf out "`@[%a@]`@ : " P.pp t
          in
          let msg = Utils.err_sprintf
              "@[<hv2>type error@ when applying @[%a%a@]@ on @[%a : %a@]@ in subst @[%a@]: %s@]"
              pp_t ae.ae_term P.pp_in_app ae.ae_ty
              (CCFormat.list P.pp_in_app) ae.ae_args
              (CCFormat.list P.pp_in_app) ae.ae_args_ty
              (Subst.pp P.pp) ae.ae_subst ae.ae_msg
          in Some msg
        | UnifError (msg, t1, t2) ->
          let module P = Print(T) in
          let msg = CCFormat.sprintf
              "@[<hv2>unification error@ for %a@ and@ %a: %s@]"
              P.pp_in_app t1 P.pp_in_app t2 msg
          in Some msg
        | _ -> None
      )

  let error_apply_ ae = raise (ApplyError ae)
  let error_unif_ msg t1 t2 = raise (UnifError (msg, t1, t2))

  let ty_apply_full t ~terms:l_terms ~tys:l_tys =
    let rec app_ ~subst t l_terms l_tys = match T.repr t, l_terms, l_tys with
      | _, [], [] -> t, subst
      | _, [], _ | _, _, [] -> assert false
      | TyBuiltin _, _, _
      | App (_,_),_, _
      | Const _, _, _ ->
        error_apply_
          {ae_msg="cannot apply this type"; ae_term=None;
           ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst}
      | Var v, _, _ ->
        begin try
            let t = Subst.find_exn ~subst v in
            app_ ~subst t l_terms l_tys
          with Not_found ->
            error_apply_
              {ae_msg="cannot apply this type"; ae_term=None;
               ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst; }
        end
      | TyMeta _,_,_ -> assert false
      | TyArrow (a, t'), _ :: l_terms', b :: l_tys' ->
        if equal_with ~subst a b
        then app_ ~subst t' l_terms' l_tys'
        else
          error_apply_
            {ae_msg="type mismatch on first argument"; ae_term=None;
             ae_ty=t; ae_args=l_terms; ae_args_ty=l_tys; ae_subst=subst; }
      | Bind (Binder.TyForall, v, t'), b :: l_terms', _ :: l_tys' ->
        let subst = Subst.add ~subst v b in
        app_ ~subst t' l_terms' l_tys'
      | _ -> assert false
    in
    app_ ~subst:Subst.empty t l_terms l_tys

  let ty_apply t ~terms ~tys =
    let t, subst = ty_apply_full t ~terms ~tys in
    if Subst.is_empty subst then t else eval ~subst t

  let ty_apply_mono t ~tys:l =
    let subst = Subst.empty in
    let rec app_ t l = match T.repr t, l with
      | _, [] -> t
      | TyBuiltin _, _
      | App (_,_),_
      | Const _, _ ->
        error_apply_
          {ae_msg="cannot apply this type"; ae_term=None;
           ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | Var _, _ ->
        error_apply_
          {ae_msg="cannot apply this type"; ae_term=None;
           ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | TyMeta _,_ -> assert false
      | TyArrow (a, t'), b :: l' ->
        if equal a b
        then app_ t' l'
        else
          error_apply_
            {ae_msg="type mismatch on first argument"; ae_term=None;
             ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst; }
      | Bind (Binder.TyForall, _, _), _ ->
        error_apply_
          {ae_msg="non monomorphic type"; ae_term=None;
           ae_ty=t; ae_args=[]; ae_args_ty=l; ae_subst=subst}
      | _ -> assert false
    in
    app_ t l

  let prop = ty_prop

  type signature = id -> t_ option

  let find_ty_ ~sigma id = match sigma id with
    | Some ty -> ty
    | None -> raise (Undefined id)

  let ty_of_signature_exn ~(sigma:signature) t =
    let rec aux t = match T.repr t with
      | Const id -> find_ty_ ~sigma id
      | Builtin b ->
        begin match b with
          | `Imply (_,_)
          | `Or _
          | `And _
          | `Not _ -> prop
          | `True
          | `False -> prop
          | `Unparsable ty -> ty
          | `Ite (_,b,_) -> aux b
          | `Eq (_,_) -> prop
          | `DataTest id ->
            (* id: a->b->tau, where tau inductive; is-id: tau->prop *)
            let ty = find_ty_ ~sigma id in
            ty_arrow (ty_returns ty) prop
          | `DataSelect (id,n) ->
            (* id: a_1->a_2->tau, where tau inductive; select-id-i: tau->a_i*)
            let ty = find_ty_ ~sigma id in
            begin match get_ty_arg ty n with
              | Some ty_arg ->
                ty_arrow (ty_returns ty) ty_arg
              | _ ->
                failwith "cannot infer type, wrong argument to DataSelect"
            end
          | `Undefined_self t -> aux t
          | `Undefined_atom (_,ty) -> ty
          | `Guard (t, _) -> aux t
        end
      | Var v -> Var.ty v
      | App (_, []) -> assert false
      | App (f,l) ->
        let ty_f = aux f in
        let tys = List.map aux l in
        begin
          try ty_apply ty_f ~terms:l ~tys
          with ApplyError ae ->
            let ae = {ae with ae_term=Some f; ae_args=l; ae_args_ty=tys; ae_ty=ty_f} in
            raise (ApplyError ae)
        end
      | Bind (b,v,t) ->
        begin match b with
          | Binder.Forall
          | Binder.Exists
          | Binder.Mu -> aux t
          | Binder.Fun ->
            if ty_returns_Type (Var.ty v)
            then ty_forall v (aux t)
            else ty_arrow (Var.ty v) (aux t)
          | Binder.TyForall -> ty_type
        end
      | Let (_,_,u) -> aux u
      | Match (_,m,_) ->
        let _, (_, rhs) = ID.Map.choose m in
        aux rhs
      | TyMeta _ -> assert false
      | TyBuiltin b ->
        begin match b with
          | `Kind -> failwith "Term_ho.ty: kind has no type"
          | `Type -> ty_kind
          | `Prop
          | `Unitype -> ty_type
        end
      | TyArrow (_,_) -> ty_type
    in aux t

  let ty_of_signature ~sigma t =
    try CCResult.return (ty_of_signature_exn ~sigma t)
    with e -> Utils.err_of_exn e

  let ty ~env t =
    try CCResult.return (ty_of_signature_exn ~sigma:(Env.find_ty ~env) t)
    with e -> Utils.err_of_exn e

  let ty_exn ~env t = ty_of_signature_exn ~sigma:(Env.find_ty ~env) t

  let info_of_ty_exn ~env ty =
    let id = head_sym_exn ty in
    Env.find_exn ~env id

  let info_of_ty ~env ty =
    try Result.Ok (info_of_ty_exn ~env ty)
    with No_head _ -> Result.Error "type has no head"

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
        | Bind _, _
        | Let (_, _, _), _
        | Match _, _ ->
          error_unif_ "pattern is not first-order" t1 t2
        (* let module P = Print(T) in
           Utils.invalid_argf "pattern `@[%a@]` is not first-order" P.pp t1 *)
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

module Default : sig
  include S

  module U : UTIL with type t_ = t
  module P : PRINT with type t = t
end = struct
  type t = {
    view: t view;
  }
  type t_ = t

  let rec repr t = match t.view with
    | TyMeta {MetaVar.deref=Some t'; _} -> repr t'
    | v -> v

  let make_raw_ view = {view}

  let build view = match view with
    | App (t, []) -> t
    | App ({view=App (f, l1); _}, l2) ->
      make_raw_ (App (f, l1 @ l2))
    | _ -> make_raw_ view

  module U = Util(struct
      type t = t_
      let repr = repr
      let build = build
    end)
  module P = Print(struct type t = t_ let repr = repr end)
end

let default = (module Default : S)

(** {2 Conversion between two representations} *)

module Convert(T1 : REPR)(T2 : BUILD)
  : sig
    val convert : T1.t -> T2.t

    val pipe : unit -> (T1.t, T2.t, 'a, 'a) Transform.t
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
        | Match (t,l,d) ->
          Match (
            convert t,
            ID.Map.map (fun (vars,rhs) -> List.map aux_var vars, convert rhs) l,
            map_default_case convert d
          )
        | TyArrow (a,b) -> TyArrow (convert a, convert b)
        | TyMeta v -> TyMeta (aux_meta v)
      )
  and aux_var v = Var.update_ty ~f:convert v
  and aux_meta v = MetaVar.update ~f:convert v

  let pipe () =
    Transform.make ~name:"convert"
      ~encode:(fun t -> convert t, ())
      ~decode:(fun () x -> x)
      ()
end
