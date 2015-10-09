
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module T1I = NunTerm_typed
module TyI = NunType_intf
module Stmt = NunProblem.Statement

type id = ID.t

let section = NunUtils.Section.make "mono"

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S

  exception InvalidProblem of string

  type mono_state
  (** State used for monomorphizing (to convert [f int (list nat)] to
      [f_int_list_nat], and back) *)

  val create : unit -> mono_state
  (** New state *)

  val monomorphize :
    ?depth_limit:int ->
    sigma:T1.ty NunProblem.Signature.t ->
    state:mono_state ->
    (T1.t, T1.ty) NunProblem.t ->
    (T2.t, T2.ty) NunProblem.t
  (** Filter and specialize definitions of the problem.

      First it finds a set of instances for each symbol
      such that it is sufficient to instantiate the corresponding (partial)
      definitions of the symbol with those tuples.

      Then it specializes relevant definitions with the set of tuples
      computed earlier.

      @param sigma signature of the problem
      @param depth_limit recursion limit for specialization of functions
      @param state used to convert forward and backward *)

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

  (* substitution *)
  module Subst = Var.Subst(struct type t = T1.ty end)

  let nop_ _ = ()

  (* convert [subst T1.ty] to [T2.ty].
     callbacks are used for non-(ground atomic types).
     @param subst the substitution for variables *)
  let convert_ty_ ?(on_non_ground=nop_) ~subst ty =
    let rec convert_ ty = match T1.Ty.view ty with
      | TyI.Kind -> T2.ty_kind
      | TyI.Type -> T2.ty_type
      | TyI.Builtin b -> T2.ty_builtin b
      | TyI.Const id -> T2.ty_const id
      | TyI.Var v ->
          (* maybe [v] is bound *)
          begin match Subst.find ~subst v with
          | None ->
              on_non_ground ty;
              T2.ty_var (Var.update_ty v ~f:convert_)
          | Some ty -> convert_ ty
          end
      | TyI.Meta _ -> assert false
      | TyI.App (f,l) ->
          T2.ty_app
            (convert_ f)
            (List.map convert_ l)
      | TyI.Arrow (a,b) ->
          T2.ty_arrow (convert_ a) (convert_ b)
      | TyI.Forall (v,t) ->
          on_non_ground ty;
          T2.ty_forall
            (Var.update_ty v ~f:convert_)
            (convert_ t)
    in
    convert_ ty

  let convert_ground_atomic_ty_ ~subst ty =
    convert_ty_ ty ~subst
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

    let rec mem tup = function
      | [] -> false
      | tup' :: l' -> ArgTuple.equal tup tup' || mem tup l'

    (* add [tup] to the set [l] *)
    let add tup l =
      if mem tup l then l else tup :: l

    let print out =
      fpf out "{@[<hv1>%a@]}" (CCFormat.list ~start:"" ~stop:"" ArgTuple.print)
  end

  (** set of tuples of parameters to instantiate a given function symbol with *)
  module SetOfInstances = struct
    type t = ArgTupleSet.t ID.Map.t (* function -> set of args *)

    let empty = ID.Map.empty

    let args t id =
      try ID.Map.find id t
      with Not_found -> ArgTupleSet.empty

    let mem t id tup = ArgTupleSet.mem tup (args t id)

    let mem_id t id = ID.Map.mem id t

    let add t id tup =
      let set =
        try ID.Map.find id t
        with Not_found -> ArgTupleSet.empty in
      let set = ArgTupleSet.add tup set in
      (* add a tuple of args for [id], and require [id] *)
      ID.Map.add id set t

    let print out t =
      fpf out "@[<hv>instances{%a@]@,}"
        (ID.Map.print ID.print_no_id ArgTupleSet.print) t
  end

  let find_ty_ ~sigma id =
    try NunProblem.Signature.find_exn ~sigma id
    with Not_found ->
      fail_ ("symbol " ^ ID.to_string id ^ " is not declared")

  module St = struct
    type depth = int

    type t = {
      axioms: (T1.t, T1.ty) NunProblem.Statement.t list ID.Tbl.t;
        (* ID -> set of axioms in which the ID is defined *)
      to_process : (ID.t * ArgTuple.t * depth) Queue.t;
        (* tuples to process (with recursion depth) *)
      mutable required: SetOfInstances.t;
        (* tuples that must be instantiated *)
      mutable processed: SetOfInstances.t;
        (* tuples already instantiated (subset of [required]) *)
    }

    let is_processed ~state id tup = SetOfInstances.mem state.processed id tup

    let required ~state id tup = SetOfInstances.mem state.required id tup

    let required_id ~state id = SetOfInstances.mem_id state.required id

    let schedule ~state ~depth id tup =
      state.required <- SetOfInstances.add state.required id tup;
      Queue.push (id,tup,depth) state.to_process

    let create () = {
      axioms=ID.Tbl.create 128;
      processed=SetOfInstances.empty;
      required=SetOfInstances.empty;
      to_process=Queue.create();
    }

    (* add dependency on [id] applied to [tup] *)
    let have_processed ~state id tup =
      state.processed <- SetOfInstances.add state.processed id tup
  end

  type mono_state = St.t
  let create = St.create

  (* take [n] ground atomic type arguments in [l], or fail *)
  let rec take_n_ground_atomic_types_ ~subst n = function
    | _ when n=0 -> []
    | [] -> failf_ "not enough arguments (%d missing)" n
    | t :: l' ->
        let t = convert_ground_atomic_ty_ ~subst t in
        t :: take_n_ground_atomic_types_ ~subst (n-1) l'

  let monomorphize ?(depth_limit=256) ~sigma ~state pb =
    (* map T1.t to T2.t and, simultaneously, compute relevant instances
       of symbols [t] depends on.
       @param subst bindings for type variables *)
    let rec conv_term ~depth ~subst t =
      match T1.view t with
      | TI.Builtin b -> T2.builtin b
      | TI.Const c ->
          St.schedule ~state ~depth:(depth+1)
            c ArgTuple.empty; (* no args, but still required *)
          T2.const c
      | TI.Var v ->
          begin match Subst.find ~subst v with
          | Some t' -> conv_term ~depth ~subst t'
          | None ->
              let v = aux_var ~subst v in
              T2.var v
          end
      | TI.App (f,l) ->
          (* XXX: WHNF would help? *)
          begin match T1.view f with
          | TI.Builtin b ->
              (* builtins are defined, but examine their args *)
              let l = List.map (conv_term ~subst ~depth) l in
              T2.app (T2.builtin b) l
          | TI.Const id ->
              (* find type arguments *)
              let ty = find_ty_ ~sigma id in
              let n = num_param_ty_ ty in
              (* tuple of arguments for [id] *)
              let tup = take_n_ground_atomic_types_ ~subst n l in
              let tup = ArgTuple.of_list tup in
              St.schedule ~state ~depth id tup;
              (* analyse all args (types and terms) *)
              let l = List.map (conv_term ~depth ~subst) l in
              T2.app (T2.const id) l
          | _ ->
              failf_ "cannot monomorphize term with head %a" P1.print f
          end
      | TI.Fun (v,t) ->
          T2.fun_ (aux_var ~subst v) (conv_term ~depth ~subst t)
      | TI.Forall (v,t) ->
          T2.forall (aux_var ~subst v) (conv_term ~depth ~subst t)
      | TI.Exists (v,t) ->
          T2.exists (aux_var ~subst v) (conv_term ~depth ~subst t)
      | TI.Let (v,t,u) ->
          T2.let_ (aux_var ~subst v)
            (conv_term ~depth ~subst t) (conv_term ~depth ~subst u)
      | TI.Ite (a,b,c) ->
          T2.ite
            (conv_term ~depth ~subst a)
            (conv_term ~depth ~subst b)
            (conv_term ~depth ~subst c)
      | TI.Eq (a,b) ->
          T2.eq (conv_term ~depth ~subst a) (conv_term ~depth ~subst b)
      | TI.TyKind -> T2.ty_kind
      | TI.TyType -> T2.ty_type
      | TI.TyMeta _ -> failwith "Mono.encode: remaining type meta-variable"
      | TI.TyBuiltin b -> T2.ty_builtin b
      | TI.TyArrow (a,b) ->
          T2.ty_arrow (conv_term ~depth ~subst a) (conv_term ~depth ~subst b)
      | TI.TyForall (v,t) ->
          (* TODO: emit warning? *)
          assert (not (Subst.mem ~subst v));
          T2.ty_forall (aux_var ~subst v) (conv_term ~depth ~subst t)
    and aux_var ~subst v =
      Var.update_ty ~f:(conv_term ~depth:0 ~subst) v
    in
    (* maps a statement to 0 to n specialized statements *)
    let aux_statement ~depth st =
      if depth>depth_limit then []
      else
        (* process statement *)
        let loc = Stmt.loc st in
        match Stmt.view st with
        | Stmt.Decl (id,k,ty) ->
            begin match k with
            | Stmt.Decl_type ->
                if St.required_id ~state id
                then
                  [ Stmt.ty_decl ?loc id (convert_ty_ ~subst:Subst.empty ty) ]
                else []
            | _ ->  assert false (* TODO *)
            end
        | Stmt.Goal t ->
            (* convert goal *)
            [ Stmt.goal ?loc (conv_term ~depth ~subst:Subst.empty t) ]
        | Stmt.Axiom s -> assert false (* TODO *)
    in
    let pb' = NunProblem.statements pb
      |> CCList.flat_map (aux_statement ~depth:0)
      |> NunProblem.make
    in
    (* some debug *)
    NunUtils.debugf ~section 3 "@[<2>instances:@ @[%a@]@]"
      SetOfInstances.print state.St.required;
    pb'

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

let pipe (type a)(type b) ~print
(module T1 : NunTerm_ho.VIEW with type t = a)
(module T2 : NunTerm_ho.S with type t = b)
=
  let module Mono = Make(T1)(T2) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T2) in
      [Format.printf "@[<2>after mono:@ %a@]@."
        (NunProblem.print P.print P.print_ty)]
    else []
  in
  NunTransform.make1
    ~on_encoded
    ~name:"monomorphization"
    ~encode:(fun p ->
      let sigma = NunProblem.signature p in
      let state = Mono.create () in
      let p = Mono.monomorphize ~sigma ~state p in
      p, state
      (* TODO mangling of types, as an option *)
    )
    ~decode:(fun _ m -> m)
    ()
