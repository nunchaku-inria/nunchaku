
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Monomorphization} *)

module ID = NunID
module Var = NunVar
module TI = NunTerm_intf
module TyI = NunType_intf
module Stmt = NunProblem.Statement

type id = ID.t

let section = NunUtils.Section.make "mono"

module type S = sig
  module T : NunTerm_ho.S

  exception InvalidProblem of string

  type mono_state
  (** State used for monomorphizing (to convert [f int (list nat)] to
      [f_int_list_nat], and back) *)

  val create : unit -> mono_state
  (** New state *)

  val monomorphize :
    ?depth_limit:int ->
    sigma:T.ty NunProblem.Signature.t ->
    state:mono_state ->
    (T.t, T.ty) NunProblem.t ->
    (T.t, T.ty) NunProblem.t
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
      (T.t,T.ty) NunProblem.t ->
      (T.t,T.ty) NunProblem.t

    val mangle_problem :
      state:state ->
      (T.t,T.ty) NunProblem.t ->
      (T.t,T.ty) NunProblem.t

    val unmangle_term : state:state -> T.t -> T.t

    val unmangle_model :
        state:state ->
        T.t NunProblem.Model.t -> T.t NunProblem.Model.t
    (** Stay in the same term representation, but de-monomorphize *)
  end
end

module Make(T : NunTerm_ho.S) : S with module T = T
= struct
  module T = T

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

  module TyUtils = TyI.Utils(T.Ty)
  module P = NunTerm_ho.Print(T)
  module TU = NunTerm_intf.Util(T)

  (* substitution *)
  module Subst = Var.Subst(struct type t = T.ty end)
  module SubstUtil = NunTerm_ho.SubstUtil(T)(Subst)
  module Red = NunReduce.Make(T)(Subst)

  (* number of parameters of this (polymorphic?) T.ty type *)
  let rec num_param_ty_ ty = match T.Ty.view ty with
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

  (* A tuple of arguments that a given function symbol should be
     instantiated with *)
  module ArgTuple = struct
    type t = {
      args: T.ty list;
      mangled: ID.t option; (* mangled name of [f args] *)
    }

    let empty = {args=[]; mangled=None;}
    let of_list ~mangled l = {args=l; mangled;}
    let args t = t.args
    let mangled t = t.mangled

    (* equality for ground atomic types T.ty *)
    let rec ty_ground_eq_ t1 t2 = match T.Ty.view t1, T.Ty.view t2 with
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

    let equal tup1 tup2 =
      CCList.equal ty_ground_eq_ tup1.args tup2.args

    let print out tup =
      let pp_mangled out = function
        | None -> ()
        | Some id -> fpf out " as %a" ID.print id
      in
      fpf out "@[%a%a@]"
        (CCFormat.list ~start:"(" ~stop:")" ~sep:", " P.print_ty) tup.args
        pp_mangled tup.mangled
  end

  module ArgTupleSet = struct
    type t = ArgTuple.t list

    let empty = []
    let to_list l = l
    let to_seq = Sequence.of_list

    let rec mem tup = function
      | [] -> false
      | tup' :: l' -> ArgTuple.equal tup tup' || mem tup l'

    (* add [tup] to the set [l] *)
    let add tup l =
      if mem tup l then l else tup :: l

    let print out =
      fpf out "@[<hv1>%a@]" (CCFormat.list ~start:"" ~stop:"" ArgTuple.print)
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
      fpf out "@[<hv>instances{@,%a@]@,}"
        (ID.Map.print ~start:"" ~stop:"" ID.print_no_id ArgTupleSet.print) t
  end

  let find_ty_ ~sigma id =
    try NunProblem.Signature.find_exn ~sigma id
    with Not_found ->
      fail_ ("symbol " ^ ID.to_string id ^ " is not declared")

  module St = struct
    type depth = int

    type t = {
      mangle : (string, ID.t) Hashtbl.t;
        (* mangled name -> mangled ID *)
      unmangle : (ID.t * T.t list) ID.Tbl.t;
        (* mangled name -> (id, args) *)
      mutable required: SetOfInstances.t;
        (* tuples that must be instantiated *)
      mutable processed: SetOfInstances.t;
        (* tuples already instantiated (subset of [required]) *)
      mutable on_schedule : depth:depth -> ID.t -> ArgTuple.t -> unit;
    }

    let is_processed ~state id tup = SetOfInstances.mem state.processed id tup

    let required_id ~state id = SetOfInstances.mem_id state.required id

    let schedule ~state ~depth id tup =
      NunUtils.debugf ~section 3 "require %a on %a" ID.print id ArgTuple.print tup;
      state.required <- SetOfInstances.add state.required id tup;
      state.on_schedule ~depth id tup

    (* find tuples to process that match [t] *)
    let find_matching ~state t =
      let id = TU.head_sym t in
      let set = SetOfInstances.args state.required id in
      ArgTupleSet.to_seq set
      |> Sequence.filter_map
        (fun tup ->
          let t2 = T.app (T.const id) (ArgTuple.args tup) in
          try
            let subst = SubstUtil.match_exn t t2 in
            Some (id, tup, subst)
          with SubstUtil.UnifError _ -> None
        )

    let create () = {
      processed=SetOfInstances.empty;
      required=SetOfInstances.empty;
      mangle=Hashtbl.create 64;
      unmangle=ID.Tbl.create 64;
      on_schedule=(fun ~depth:_ _ _ -> ());
    }

    let find_tuples ~state id = SetOfInstances.args state.required id

    let reset_on_schedule ~state =
      state.on_schedule <- (fun ~depth:_ _ _ -> ())

    (* remember that (id,tup) -> mangled *)
    let save_mangled ~state id tup ~mangled =
      try Hashtbl.find state.mangle mangled
      with Not_found ->
        (* create new ID *)
        let mangled' = ID.make ~name:mangled in
        Hashtbl.add state.mangle mangled mangled';
        ID.Tbl.replace state.unmangle mangled' (id, tup);
        mangled'

    (* add dependency on [id] applied to [tup] *)
    let has_processed ~state id tup =
      state.processed <- SetOfInstances.add state.processed id tup
  end

  type mono_state = St.t
  let create = St.create

  (* find a specialized name for [id tup] if [tup] not empty *)
  let mangle_ ~state id args =
    let pp_list p = CCFormat.list ~start:"" ~stop:"" ~sep:"_" p in
    let rec flat_ty_ out t = match T.Ty.view t with
      | TyI.Kind -> CCFormat.string out "kind"
      | TyI.Type -> CCFormat.string out "type"
      | TyI.Builtin b -> CCFormat.string out (NunBuiltin.Ty.to_string b)
      | TyI.Const id -> ID.print_no_id out id
      | TyI.Var _ -> fail_ "mangling: cannot mangle variable"
      | TyI.Meta _ -> assert false
      | TyI.App (f,l) ->
          fpf out "%a_%a" flat_ty_ f (pp_list flat_ty_) l
      | TyI.Arrow (a,b) -> fpf out "%a_to_%a" flat_ty_ a flat_ty_ b
      | TyI.Forall (_,_) -> failf_ "mangling: cannot mangle %a" P.print_ty t
    in
    match args with
    | [] -> id, None
    | _::_ ->
      let name = CCFormat.sprintf "@[<h>%a@]" flat_ty_ (T.app (T.const id) args) in
      let mangled = St.save_mangled ~state id args ~mangled:name in
      mangled, Some mangled

  (* find a case matching [id tup] in [cases], or None *)
  let find_case_ ~subst ~cases id tup =
    let t = T.app (T.const id) (ArgTuple.args tup) in
    CCList.find_map
      (fun case ->
        match SubstUtil.match_ ~subst2:subst case.Stmt.case_defined t with
        | None -> None
        | Some subst' -> Some (case, subst')
      )
      cases

  let monomorphize ?(depth_limit=256) ~sigma ~state pb =
    (* map T.t to T.t and, simultaneously, compute relevant instances
       of symbols [t] depends on.
       @param subst bindings for type variables
       @param f called on every schedule
       @param mangle enable/disable mangling (in types...)
      *)
    let rec conv_term ~mangle ~depth ~subst t =
      match T.view t with
      | TI.Builtin b -> T.builtin b
      | TI.Const c ->
          (* no args, but we require [c] in the output *)
          St.schedule ~state ~depth:(depth+1) c ArgTuple.empty;
          T.const c
      | TI.Var v ->
          begin match Subst.find ~subst v with
          | Some t' -> conv_term ~mangle ~depth ~subst t'
          | None ->
              let v = aux_var ~subst v in
              T.var v
          end
      | TI.App (f,l) ->
          (* first, beta-reduce locally *)
          let f, l, subst = Red.Full.whnf ~subst f l in
          begin match T.view f with
          | TI.Fun _ -> assert false (* beta-reduction failed? *)
          | TI.Builtin b ->
              (* builtins are defined, but examine their args *)
              let l = List.map (conv_term ~mangle ~subst ~depth) l in
              T.app (T.builtin b) l
          | TI.Const id ->
              (* find type arguments *)
              let ty = find_ty_ ~sigma id in
              let n = num_param_ty_ ty in
              (* tuple of arguments for [id] *)
              let tup = take_n_ground_atomic_types_ ~depth ~subst n l in
              (* mangle? *)
              let new_id, mangled =
                if mangle then mangle_ ~state id tup
                else id, None
              in
              (* schedule specialization of [id] *)
              let tup = ArgTuple.of_list ~mangled tup in
              St.schedule ~state ~depth:(depth+1) id tup;
              (* convert arguments.
                 Drop type arguments iff they are mangled with ID *)
              let l = if mangled=None then l else CCList.drop n l in
              let l = List.map (conv_term ~mangle ~depth ~subst) l in
              T.app (T.const new_id) l
          | _ ->
              failf_ "cannot monomorphize term with head %a" P.print f
          end
      | TI.Fun (v,t) ->
          T.fun_ (aux_var ~subst v) (conv_term ~mangle ~depth ~subst t)
      | TI.Forall (v,t) ->
          T.forall (aux_var ~subst v) (conv_term ~mangle ~depth ~subst t)
      | TI.Exists (v,t) ->
          T.exists (aux_var ~subst v) (conv_term ~mangle ~depth ~subst t)
      | TI.Let (v,t,u) ->
          T.let_ (aux_var ~subst v)
            (conv_term ~mangle ~depth ~subst t)
            (conv_term ~mangle ~depth ~subst u)
      | TI.Ite (a,b,c) ->
          T.ite
            (conv_term ~mangle ~depth ~subst a)
            (conv_term ~mangle ~depth ~subst b)
            (conv_term ~mangle ~depth ~subst c)
      | TI.Eq (a,b) ->
          T.eq
            (conv_term ~mangle ~depth ~subst a)
            (conv_term ~mangle ~depth ~subst b)
      | TI.TyKind -> T.ty_kind
      | TI.TyType -> T.ty_type
      | TI.TyMeta _ -> failwith "Mono.encode: remaining type meta-variable"
      | TI.TyBuiltin b -> T.ty_builtin b
      | TI.TyArrow (a,b) ->
          T.ty_arrow
            (conv_term ~mangle ~depth ~subst a)
            (conv_term ~mangle ~depth ~subst b)
      | TI.TyForall (v,t) ->
          (* TODO: emit warning? *)
          assert (not (Subst.mem ~subst v));
          T.ty_forall
            (aux_var ~subst v)
            (conv_term ~mangle ~depth ~subst t)

    and aux_var ~subst v =
      Var.update_ty ~f:(conv_term ~mangle:false ~depth:0 ~subst) v

    (* take [n] ground atomic type arguments in [l], or fail *)
    and take_n_ground_atomic_types_ ~depth ~subst n = function
      | _ when n=0 -> []
      | [] -> failf_ "not enough arguments (%d missing)" n
      | t :: l' ->
          (* do not mangle types *)
          let t = conv_term ~depth ~mangle:false ~subst t in
          t :: take_n_ground_atomic_types_ ~depth ~subst (n-1) l'
    in

    (* specialize mutual cases *)
    let aux_cases ~subst cases =
      let q = Queue.create () in (* task list, for the fixpoint *)
      let res = ref [] in (* resulting axioms *)
      (* if we required monomorphization of [id tup], and some case in [l]
         matches [id tup], then push into the queue so that it will be
         processed in the fixpoint *)
      let on_schedule ~depth id tup =
        match find_case_ ~subst ~cases id tup with
        | None -> ()
        | Some (case, subst) ->
            Queue.push (id, tup, depth, case, subst) q
      in
      state.St.on_schedule <- on_schedule;
      (* push already required tuples into the queue *)
      List.iter
        (fun case ->
          St.find_matching ~state case.Stmt.case_defined
          |> Sequence.iter
            (fun (id, tup, subst) -> Queue.push (id, tup, 0, case, subst) q)
        ) cases;
      (* fixpoint *)
      while not (Queue.is_empty q) do
        let id, tup, depth, case, subst = Queue.take q in
        (* check for depth limit and loops *)
        if depth > depth_limit
        || St.is_processed ~state id tup then ()
        else (
          NunUtils.debugf ~section 3
            "@[<2>process case `%a` for@ (%a %a)@ at depth %d@]"
            P.print case.Stmt.case_defined ID.print_no_id id ArgTuple.print tup depth;
          (* avoid loops *)
          St.has_processed ~state id tup;
          (* we know [subst case.defined = (id args)], now
              specialize the axioms of case and output them *)
          let subst = Subst.add ~subst case.Stmt.case_alias case.Stmt.case_defined in
          List.iter
            (fun ax ->
              (* monomorphize axiom, and push it in res *)
              let ax = conv_term ~subst ~depth:(depth+1) ~mangle:true ax in
              CCList.Ref.push res ax
            )
            case.Stmt.case_axioms
        )
      done;
      (* remove callback *)
      St.reset_on_schedule ~state;
      !res
    in

    (* maps a statement to 0 to n specialized statements *)
    let aux_statement st =
      NunUtils.debugf ~section 2 "@[<2>convert statement@ `%a`@]"
        (NunProblem.Statement.print P.print P.print_ty) st;
      (* process statement *)
      let loc = Stmt.loc st in
      match Stmt.view st with
      | Stmt.Decl (id,k,ty) ->
          begin match k with
          | Stmt.Decl_type ->
              if St.required_id ~state id
              then (* type is needed, keep it *)
                [ Stmt.ty_decl ?loc id
                    (conv_term ~mangle:false ~depth:0 ~subst:Subst.empty ty) ]
              else []
          | Stmt.Decl_fun
          | Stmt.Decl_prop ->
              let tuples = St.find_tuples ~state id in
              (* for each tuple that requires [id], specialize *)
              List.map
                (fun tup ->
                  (* apply type to tuple *)
                  let ty = SubstUtil.ty_apply ty (ArgTuple.args tup) in
                  (* require symbols in the type *)
                  let ty = conv_term ~mangle:false ~depth:0 ~subst:Subst.empty ty in
                  (* return new statement *)
                  let new_id = match ArgTuple.mangled tup with
                    | None -> id
                    | Some x -> x
                  in
                  Stmt.mk_decl ?loc new_id k ty)
                (ArgTupleSet.to_list tuples)
          end
      | Stmt.Goal t ->
          (* convert goal *)
          [ Stmt.goal ?loc (conv_term ~mangle:true ~depth:0 ~subst:Subst.empty t) ]
      | Stmt.Axiom (Stmt.Axiom_std l) ->
          let l = List.map (conv_term ~mangle:true ~depth:0 ~subst:Subst.empty) l in
          [ Stmt.axiom ?loc l ]
      | Stmt.Axiom (Stmt.Axiom_spec l) ->
          let l = aux_cases ~subst:Subst.empty l in
          [ Stmt.axiom ?loc l ]
      | Stmt.Axiom (Stmt.Axiom_rec l) ->
          let l = aux_cases ~subst:Subst.empty l in
          [ Stmt.axiom ?loc l ]
      | Stmt.TyDef (k, l) ->
          assert false (* TODO: fixpoint again *)
    in
    let pb' = NunProblem.statements pb
      |> List.rev (* start at the end *)
      |> CCList.flat_map aux_statement
      |> List.rev
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
      rev: T.t ID.Tbl.t; (* new identifier -> monomorphized term *)
    }

    let create () = {
      tree=Trie.empty;
      rev=ID.Tbl.create 64;
    }

    let mangle_term ~state:_ _ = assert false (* TODO: traverse term, use trie *)

    let mangle_problem ~state pb =
      NunProblem.map ~term:(mangle_term ~state) ~ty:(mangle_term ~state) pb

    let unmangle_term ~state:_ _ = assert false (* TODO reverse mapping *)

    let unmangle_model ~state m =
      NunProblem.Model.map ~f:(unmangle_term ~state) m
  end
end

let pipe (type a) ~print
(module T : NunTerm_ho.S with type t = a)
=
  let module Mono = Make(T) in
  let on_encoded = if print
    then
      let module P = NunTerm_ho.Print(T) in
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
