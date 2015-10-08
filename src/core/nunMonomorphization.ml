
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module T1I = NunTerm_typed
module TyI = NunType_intf
module St = NunProblem.Statement

type id = ID.t

let section = NunUtils.Section.make "mono"

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  exception InvalidProblem of string

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
    val is_empty : t -> bool
    val add : ArgTuple.t -> t -> t
    val to_list : t -> ArgTuple.t list
  end

  module SetOfInstances : sig
    type t

    val args : t -> id -> ArgTupleSet.t
    (** function -> set of args to instantiate it with *)

    val required : t -> id -> bool
    (** Is the symbol even needed? *)
  end

  type mono_state
  (** State used for monomorphizing (to convert [f int (list nat)] to
      [f_int_list_nat], and back) *)

  val create : unit -> mono_state
  (** New state *)

  val compute_instances :
    sigma:T1.ty NunProblem.Signature.t ->
    (T1.t, T1.ty) NunProblem.t ->
    SetOfInstances.t
  (** [compute_instances pb] finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples
      @param the signature of the symbols *)

  val monomorphize :
    instances:SetOfInstances.t ->
    state:mono_state ->
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

  exception InvalidProblem of string

  let () = Printexc.register_printer
    (function
      | InvalidProblem msg -> Some ("invalid problem: " ^ msg)
      | _ -> None
    )

  let fpf = Format.fprintf

  let fail_ msg = raise (InvalidProblem msg)
  let failf_ msg =
    NunUtils.exn_ksprintf msg ~f:(fun msg -> raise (InvalidProblem msg))

  module TyUtils = TyI.Utils(T1.Ty)
  module P1 = NunTerm_ho.Print(T1)
  module P2 = NunTerm_ho.Print(T2)

  (* number of parameters of this (polymorphic?) T1.ty type *)
  let rec num_param_ty_ ty = match T1.Ty.view ty with
    | TyI.Var _
    | TyI.Const _
    | TyI.Kind
    | TyI.App _
    | TyI.Type -> 0
    | TyI.Meta _ -> fail_ "remaining meta-variable"
    | TyI.Builtin _ -> 0
    | TyI.Arrow (_,t') ->
        if TyUtils.is_Type t'
          then 1 + num_param_ty_ t'
          else 0  (* asks for term parameters *)
    | TyI.Forall (_,t) -> 1 + num_param_ty_ t

  let nop_ _ = ()

  (* convert [T1.ty] to [T2.ty].
     callbacks are used for non-(ground atomic types) *)
  let convert_ty_ ?(on_non_ground=nop_) ty =
    let rec convert_ty_ ty = match T1.Ty.view ty with
      | TyI.Kind -> T2.ty_kind
      | TyI.Type -> T2.ty_type
      | TyI.Builtin b -> T2.ty_builtin b
      | TyI.Const id -> T2.ty_const id
      | TyI.Var v ->
          on_non_ground ty;
          T2.ty_var (Var.update_ty v ~f:convert_ty_)
      | TyI.Meta _ -> assert false
      | TyI.App (f,l) ->
          T2.ty_app
            (convert_ty_ f)
            (List.map convert_ty_ l)
      | TyI.Arrow (a,b) ->
          T2.ty_arrow (convert_ty_ a) (convert_ty_ b)
      | TyI.Forall (v,t) ->
          on_non_ground ty;
          T2.ty_forall
            (Var.update_ty v ~f:convert_ty_)
            (convert_ty_ t)
    in
    convert_ty_ ty

  let convert_ground_atomic_ty_ ty =
    convert_ty_ ty
      ~on_non_ground:(fun ty ->
        failf_ "non-ground type: %a" P1.print_ty ty
      )

  (* A tuple of arguments that a given function symbol should be
     instantiated with *)
  module ArgTuple = struct
    type t = T2.ty list

    let empty = []
    let of_list l = l
    let to_list l = l
    let to_seq = Sequence.of_list

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
    let is_empty = CCList.is_empty
    let to_list l = l

    (* add [tup] to the set [l] *)
    let rec add tup l = match l with
      | [] -> [tup]
      | tup' :: l' ->
          if ArgTuple.equal tup tup' then l else tup' :: add tup l'

    let print out =
      fpf out "{@[<hv1>%a@]}" (CCFormat.list ~start:"" ~stop:"" ArgTuple.print)
  end

  (** set of tuples of parameters to instantiate a given function symbol with *)
  module SetOfInstances = struct
    type t = {
      args: ArgTupleSet.t ID.Map.t; (* function -> set of args *)
      required: ID.Set.t;  (* symbols that are needed *)
    }

    let empty = {
      args=ID.Map.empty;
      required=ID.Set.empty;
    }

    let required t id = ID.Set.mem id t.required

    let args t id =
      try ID.Map.find id t.args
      with Not_found -> ArgTupleSet.empty

    (* add the set of ID occuring in [ty] to [required] *)
    let add_ty_ids_ required ty =
      let module TyUtils2 = NunType_intf.Utils(T2.Ty) in
      TyUtils2.to_seq ty
      |> Sequence.filter_map
        (fun ty -> match T2.Ty.view ty with
          | TyI.Const id -> Some id
          | _ -> None
        )
      |> Sequence.fold (fun set id -> ID.Set.add id set) required

    let add t id tup =
      let set =
        try ID.Map.find id t.args
        with Not_found -> ArgTupleSet.empty in
      let set = ArgTupleSet.add tup set in
      (* add a tuple of args for [id], and require [id] *)
      let args = ID.Map.add id set t.args in
      let required = ID.Set.add id t.required in
      (* also require symbols of types in [tup] *)
      let required = ArgTuple.to_seq tup
        |> Sequence.fold add_ty_ids_ required
      in
      { args; required; }

    let print out t =
      let pp_required out r =
        fpf out "@[%a@]" (ID.Set.print ID.print_no_id) r in
      let pp_args out a =
        fpf out "@[<hv>%a@]" (ID.Map.print ID.print_no_id ArgTupleSet.print) a
      in
      fpf out "@[<hv2>instances{@,required=@[%a@],@ args=@[%a@]@]@,}"
        pp_required t.required pp_args t.args
  end

  let find_ty_ ~sigma id =
    try NunProblem.Signature.find_exn ~sigma id
    with Not_found ->
      fail_ ("symbol " ^ ID.to_string id ^ " is not declared")

  (* take [n] ground atomic type arguments in [l], or fail *)
  let rec take_n_ground_atomic_types_ n = function
    | _ when n=0 -> []
    | [] -> failf_ "not enough arguments (%d missing)" n
    | t :: l' ->
        let t = convert_ground_atomic_ty_ t in
        t :: take_n_ground_atomic_types_ (n-1) l'

  (* computes ID -> set_of_instances for every ID defined/declared in
      the list of statements [st_l] *)
  let compute_instances ~sigma pb =
    (* discover the argument tuples used for functions or type constructors in [t].
       the arguments should be ground (contain no variables) *)
    let rec analyse_term t instances =
      match T1.view t with
      | TI.Const id ->
          SetOfInstances.add instances id ArgTuple.empty
      | TI.Builtin _
      | TI.Var _ -> instances
      | TI.App (f,l) ->
          (* XXX: WHNF would help? *)
          begin match T1.view f with
          | TI.Builtin _ ->
              (* builtins are defined, but examine their args *)
              List.fold_right analyse_term l instances
          | TI.Const id ->
              (* find type arguments *)
              let ty = find_ty_ ~sigma id in
              let n = num_param_ty_ ty in
              (* tuple of arguments for [id] *)
              let tup = take_n_ground_atomic_types_ n l in
              let tup = ArgTuple.of_list tup in
              let instances = SetOfInstances.add instances id tup in
              (* analyse all args (types and terms) *)
              List.fold_right analyse_term l instances
          | _ ->
              failf_ "cannot monomorphize term with head %a" P1.print f
          end
      | TI.Fun (_,t)
      | TI.Forall (_,t)
      | TI.Exists (_,t) ->
          analyse_term t instances
      | TI.Let (_,t,u) ->
          instances |> analyse_term t |> analyse_term u
      | TI.Ite (a,b,c) ->
          instances |> analyse_term a |> analyse_term b |> analyse_term c
      | TI.Eq (a,b) ->
          instances |> analyse_term a |> analyse_term b
      | TI.TyKind
      | TI.TyType
      | TI.TyBuiltin _ -> instances
      | TI.TyArrow (a,b) -> instances |> analyse_term a |> analyse_term b
      | TI.TyForall (_,t) -> analyse_term t instances
      | TI.TyMeta _ -> assert false
    in
    (* perform analysis on one statement *)
    let analyse_statement ~instances st = match St.view st with
      | St.TyDecl (id,ty)
      | St.Decl (id,ty) ->
          (* if [id] is required, then its type must be declared *)
          if SetOfInstances.required instances id
          then analyse_term ty instances
          else instances
      | St.Def (id,_,t)
      | St.PropDef (id,_,t) ->
          if SetOfInstances.required instances id
          then analyse_term t instances
          else instances
      | St.Axiom t ->
          (* need it anyway *)
          analyse_term t instances
      | St.Goal t ->
          (* where we start *)
          analyse_term t instances
    in
    (* NOTE: we fold from the right, because statements can only depend
       on statements that come before them in the list, so the
       last statement is not depended upon *)
    let st_l = NunProblem.statements pb in
    let instances = List.fold_right
      (fun st instances ->
        NunUtils.debugf ~section 2 "@[<2>analysing@ `@[%a@]`@]"
          (NunProblem.Statement.print P1.print P1.print_ty) st;
        analyse_statement ~instances st
        )
      st_l SetOfInstances.empty
    in
    NunUtils.debugf ~section 3 "@[<2>results:@ @[%a@]@]" SetOfInstances.print instances;
    instances

  type mono_state = unit (* TODO *)

  let create () = ()

  let monomorphize ~instances ~state pb =
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
      | St.TyDecl (id,ty) ->
          (* declare type only if required *)
          (* TODO: need specialization of types too? *)
          if SetOfInstances.required instances id
          then [ St.ty_decl ?loc id (convert_ty_ ty) ]
          else []
      | St.Decl (id,ty) ->
          (* declare type only if required *)
          (* TODO: need specialization of types too? *)
          if SetOfInstances.required instances id
          then [ St.decl ?loc id (convert_ty_ ty) ]
          else []
      | St.Def (id,ty,t) ->
          if SetOfInstances.required instances id
          then
            let tuples = SetOfInstances.args instances id
              |> ArgTupleSet.to_list
              |> List.map ArgTuple.to_list
            in
            CCList.flat_map
              (fun tup ->
                assert false (* TODO specialize def here *)
              ) tuples
          else []
      | St.PropDef (id,prop,t) ->
          if SetOfInstances.required instances id
          then
            let tuples = SetOfInstances.args instances id
              |> ArgTupleSet.to_list
              |> List.map ArgTuple.to_list
            in
            CCList.flat_map
              (fun tup ->
                assert false (* TODO specialize def here *)
              ) tuples
          else []
      | St.Goal t ->
          (* convert goal *)
          [ St.goal ?loc (aux t) ]
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


