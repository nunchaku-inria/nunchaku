
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module T1I = NunTerm_typed
module TyI = NunType_intf
module St = NunProblem.Statement

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  (** {6 Set of Instances} *)

  (** Tuple of arguments to instantiate a symbol definition with *)
  module ArgTuple : sig
    type t
    val of_list : T2.ty list -> t
    val to_list : t -> T2.ty list
  end

  (** Set of {!ArgTuple.t} *)
  module ArgTupleSet : sig
    type t
    val empty : t
    val add : ArgTuple.t -> t -> t
    val to_list : t -> ArgTuple.t list
  end

  type set_of_instances =
    | NoInstances
    | Instances of ArgTupleSet.t

  val compute_instances :
    (T1.t, T1.ty) NunProblem.t ->
    set_of_instances NunID.Map.t
  (** [compute_instances pb] finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples *)

  val monomorphize :
    instances:set_of_instances NunID.Map.t ->
    (T1.t, T1.ty) NunProblem.t ->
    (T2.t, T2.ty) NunProblem.t
  (** Filter and specialize definitions of the problem using the given
      set of instances *)

  (** {6 Convert atomic types to symbols} *)
  module Mangling : sig
    type state
    (** Useful for decoding *)

    val create : unit -> state

    val mangle_term :
      state:state ->
      (T2.t,T2.ty) NunProblem.t ->
      (T2.t,T2.ty) NunProblem.t

    val mangle_problem :
      state:state ->
      (T2.t,T2.ty) NunProblem.t ->
      (T2.t,T2.ty) NunProblem.t

    val unmangle_term : state:state -> T2.t -> T2.t

    val unmangle_model :
        state:state ->
        T2.t NunProblem.Model.t -> T2.t NunProblem.Model.t
    (** Stay in the same term representation, but de-monomorphize *)
  end
end

module Make(T1 : NunTerm_ho.VIEW)(T2 : NunTerm_ho.S)
  : S with module T1 = T1 and module T2 = T2
= struct
  module T1 = T1
  module T2 = T2

  let fail_ msg = failwith ("monomorphization failed: "^msg)
  let fpf = Format.fprintf

  module TyUtils = TyI.Utils(T1.Ty)
  module P2 = NunTerm_ho.Print(T2)

  (* number of parameters of this (polymorphic?) T1.ty type *)
  let rec num_param_ty_ ty = match T1.Ty.view ty with
    | TyI.Var _
    | TyI.Const _
    | TyI.Kind
    | TyI.Type -> 0
    | TyI.App _
    | TyI.Meta _ -> fail_ "remaining meta-variable"
    | TyI.Builtin _ -> 0
    | TyI.Arrow (_,t') ->
        if TyUtils.is_Type t'
          then 1 + num_param_ty_ t'
          else 0  (* asks for term parameters *)
    | TyI.Forall (_,t) -> 1 + num_param_ty_ t

  (* A tuple of arguments that a given function symbol should be
     instantiated with *)
  module ArgTuple = struct
    type t = T2.ty list

    let of_list l = l
    let to_list l = l

    (* equality for ground atomic types T2.ty *)
    let rec ty_ground_eq_ t1 t2 = match T2.Ty.view t1, T2.Ty.view t2 with
      | TyI.Kind, TyI.Kind
      | TyI.Type, TyI.Type -> true
      | TyI.Builtin b1, TyI.Builtin b2 -> NunBuiltin.Ty.equal b1 b2
      | TyI.Const id1, TyI.Const id2 -> ID.equal id1 id2
      | TyI.App (f1,l1), TyI.App (f2,l2) ->
          ty_ground_eq_ f1 f2 && CCList.equal ty_ground_eq_ l1 l2
      | TyI.Arrow (a1,b1), TyI.Arrow (a2,b2) ->
          ty_ground_eq_ a1 a2 && ty_ground_eq_ b1 b2
      | TyI.Kind, _
      | TyI.Type, _
      | TyI.Const _, _
      | TyI.App _, _
      | TyI.Builtin _, _
      | TyI.Arrow _, _ -> false
      | TyI.Var _,_
      | TyI.Meta _,_
      | TyI.Forall (_,_),_ -> fail_ "type is not ground"

    let equal = CCList.equal ty_ground_eq_

    let print out =
      fpf out "@[%a@]"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:", " P2.print_ty)
  end

  module ArgTupleSet = struct
    type t = ArgTuple.t list

    let empty = []
    let to_list l = l

    (* add [tup] to the set [l] *)
    let rec add tup l = match l with
      | [] -> [tup]
      | tup' :: l' ->
          if ArgTuple.equal tup tup' then l else tup' :: add tup l'
  end

  (* set of tuples of parameters to instantiate a given function symbol with *)
  type set_of_instances =
    | NoInstances
    | Instances of ArgTupleSet.t

  (* computes ID -> set_of_instances for every ID defined/declared in
      the list of statements [st_l] *)
  let compute_instances st_l = assert false

  (* TODO: the encoding itself
      - detect polymorphic functions
      - specialize them on some ground type (skolem?)
      - declare f_alpha : (typeof f) applied to alpha
      - add (f alpha) -> f_alpha in [rev]
      - rewrite (f alpha) into f_alpha everywhere

      - dependency analysis from the goal, to know which specialization
        are needed
      - variations on Axiom to help removing useless things
        ("spec" for consistent axioms that can be ignored,
        "def" for terminating ones that can be ignored (> spec), etc.)
  *)

  (* TODO: specialize definitions for their tuples of types *)
  let monomorphize ~instances pb =
    (* map T1.t to T2.t *)
    let rec aux t = match T1.view t with
      | TI.Builtin b -> T2.builtin b
      | TI.Const c -> T2.const c
      | TI.Var v -> T2.var (aux_var v)
      | TI.App (f,l) -> T2.app (aux f) (List.map aux l)
      | TI.Fun (v,t) -> T2.fun_ (aux_var v) (aux t)
      | TI.Forall (v,t) -> T2.forall (aux_var v) (aux t)
      | TI.Exists (v,t) -> T2.exists (aux_var v) (aux t)
      | TI.Let (v,t,u) -> T2.let_ (aux_var v) (aux t) (aux u)
      | TI.Ite (a,b,c) -> T2.ite (aux a) (aux b) (aux c)
      | TI.Eq (a,b) -> T2.eq (aux a) (aux b)
      | TI.TyKind -> T2.ty_kind
      | TI.TyType -> T2.ty_type
      | TI.TyMeta _ -> failwith "Mono.encode: type meta-variable"
      | TI.TyBuiltin b -> T2.ty_builtin b
      | TI.TyArrow (a,b) -> T2.ty_arrow (aux a) (aux b)
      | TI.TyForall (v,t) -> T2.ty_forall (aux_var v) (aux t)
    and aux_var = Var.update_ty ~f:aux in
    (* maps a statement to 0 to n specialized statements *)
    let aux_statement st =
      let loc = St.loc st in
      match St.view st with
      | St.Axiom t ->
          (* must keep axiom, in general *)
          [St.axiom ?loc (aux t)]
      | St.TyDecl (_,_)
      | St.Decl (_,_)
      | St.Def (_,_,_)
      | St.PropDef (_,_,_)
      | St.Goal _ -> assert false (* TODO *)
    in
    NunProblem.statements pb
    |> CCList.flat_map aux_statement
    |> NunProblem.make

  (* TODO *)
  module Mangling = struct
    module Trie = CCTrie.Make(struct
      type char_ = ID.t
      let compare = ID.compare
      type t = ID.t list
      let of_list l = l
      let to_seq = Sequence.of_list
    end)

    (* the state contains:

      - a prefix tree for rewriting application such as [f a b] into [f_a_b]
      - a reverse table to remember [f_a_b -> f a b] for decoding models
    *)

    type state = {
      mutable tree: ID.t Trie.t; (* [f a b --> f_a_b] *)
      rev: T2.t ID.Tbl.t; (* new identifier -> monomorphized term *)
    }

    let create () = {
      tree=Trie.empty;
      rev=ID.Tbl.create 64;
    }

    let mangle_term ~state t = assert false (* TODO: traverse term, use trie *)

    let mangle_problem ~state pb =
      NunProblem.map ~term:(mangle_term ~state) ~ty:(mangle_term ~state) pb

    let unmangle_term ~state t = assert false (* TODO reverse mapping *)

    let unmangle_model ~state m =
      NunProblem.Model.map ~f:(unmangle_term ~state) m
  end
end


