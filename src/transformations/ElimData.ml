
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Datatypes} *)

open Nunchaku_core

module TI = TermInner
module Subst = Var.Subst
module Stmt = Statement
module T = TermInner.Default
module U = T.U
module P = T.P
module PStmt = Stmt.Print(P)(P)
module AT = AnalyzeType.Make(T)

type mode =
  | M_data
  | M_codata

let pp_mode out = function
  | M_data -> CCFormat.string out "data"
  | M_codata -> CCFormat.string out "codata"

module type S = sig
  type decode_state

  val mode : mode

  val name : string

  val transform_pb :
    (T.t, T.t) Problem.t ->
    (T.t, T.t) Problem.t * decode_state

  val decode_model :
    decode_state -> (T.t, T.t) Model.t -> (T.t, T.t) Model.t

  val pipe :
    print:bool ->
    check:bool ->
    ((T.t,T.t) Problem.t,
     (T.t,T.t) Problem.t,
     (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
    ) Transform.t

  val pipe_with :
    ?on_decoded:('d -> unit) list ->
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((T.t,T.t) Problem.t,
     (T.t,T.t) Problem.t, 'c, 'd
    ) Transform.t
end

module Make(M : sig val mode : mode end) = struct
  let mode = M.mode
  let name = CCFormat.sprintf "elim_%a" pp_mode mode
  let section = Utils.Section.make name

  exception Error of string

  let () = Printexc.register_printer
      (function
        | Error msg -> Some (Utils.err_sprintf "@[%s:@ %s@]" name msg)
        | _ -> None)

  let error msg = raise (Error msg)
  let errorf msg = Utils.exn_ksprintf ~f:error msg

  type ty = T.t

  (* the constructions to encode *)
  type to_encode =
    | Test of ID.t
    | Select of ID.t * int
    | Axiom_rec (* recursive function used for eq_corec/acyclicity axioms *)
    | Cstor of ID.t (* constructor *)

  let equal_to_encode a b = match a, b with
    | Test a, Test b
    | Cstor a, Cstor b -> ID.equal a b
    | Select (a,i), Select (b,j) -> i=j && ID.equal a b
    | Axiom_rec, Axiom_rec -> true
    | Test _, _ | Cstor _, _ | Select _, _ | Axiom_rec, _ -> false

  let hash_to_encode = function
    | Test a -> Hashtbl.hash (ID.hash a, "test")
    | Select (a,i) -> Hashtbl.hash (ID.hash a, "select", i)
    | Axiom_rec -> Hashtbl.hash "axiom_rec"
    | Cstor a -> Hashtbl.hash (ID.hash a, "const")

  module Tbl = CCHashtbl.Make(struct
      type t = to_encode
      let equal = equal_to_encode
      let hash = hash_to_encode
    end)

  type encoded_cstor = {
    ecstor_cstor: (ID.t * ty);
    ecstor_test: (ID.t * ty);
    ecstor_proj: (ID.t * ty) list;
  }

  (* encoded type *)
  type encoded_ty = {
    ety_id: ID.t;
    ety_cstors: encoded_cstor list;
    ety_card: Cardinality.t;
  }

  type state = {
    decode: to_encode ID.Tbl.t;
    (* map translated symbols (cstor/select) to original symbols *)
    tys: encoded_ty ID.Tbl.t;
    (* (co)data -> its encoding *)
    map: ID.t Tbl.t;
    (* map constructors/test/selectors to be encoded,
       into corresponding identifiers *)
    env: (T.t, T.t) Env.t;
    (* environment *)
    at_cache: AT.cache;
    (* used for computing type cardinalities *)
  }

  type decode_state = state

  let create_state ~env () = {
    decode=ID.Tbl.create 16;
    tys=ID.Tbl.create 16;
    map=Tbl.create 16;
    env;
    at_cache=AT.create_cache();
  }

  (* FIXME: replace quantifiers over infinite datatypes with the proper
     approximation? (false, depending on polarity) *)

  let get_select_ state id i : ID.t option = Tbl.get state.map (Select(id,i))

  let get_select_exn_ state id i : ID.t = match get_select_ state id i with
    | Some res -> res
    | None -> errorf "could not find encoding of `select-%a-%d`" ID.print id i

  let get_test_ state id : ID.t option = Tbl.get state.map (Test id)

  let get_test_exn state id : ID.t = match get_test_ state id with
    | Some res -> res
    | None -> errorf "could not find encoding of `is-%a`" ID.print id

  let rec tr_term state t : T.t = match T.repr t with
    | TI.Const id ->
      (* constant constructor, or unrelated ID *)
      begin match Tbl.get state.map (Cstor id) with
        | None -> t
        | Some id' ->
          (* [c asserting is-c c] *)
          let t' = U.const id' in
          let guard = U.app_const (get_test_exn state id) [t'] in
          U.asserting t' [guard]
      end
    | TI.App (f, l) ->
      begin match T.repr f with
        | TI.Const f_id ->
          let l' = List.map (tr_term state) l in
          begin match Tbl.get state.map (Cstor f_id) with
            | None ->
              U.app_const f_id l'
            | Some f_id' ->
              (* id is a constructor, we introduce a guard stating
                 [is-id (id x1..xn) & And_k proj-id-k (id x1..xn) = x_k] *)
              let t' = U.app_const f_id' l' in
              let guard =
                U.app_const (get_test_exn state f_id) [t']
                :: List.mapi
                    (fun i arg ->
                       U.eq arg (U.app_const (get_select_exn_ state f_id i) [t']))
                    l'
              in
              U.asserting t' guard
          end
        | _ -> tr_term_aux state t
      end
    | TI.Builtin (`DataSelect (id,i)) ->
      begin match get_select_ state id i with
        | Some id' -> U.const id'
        | None ->
          if mode = M_data
          then errorf "could not find encoding of `select-%a-%d`" ID.print id i
          else t
      end
    | TI.Builtin (`DataTest id) ->
      begin match get_test_ state id with
        | Some id' -> U.const id'
        | None ->
          if mode = M_data
          then errorf "could not find encoding of `is-%a`" ID.print id
          else t
      end
    | TI.Match _ ->
      errorf "expected pattern-matching to be encoded,@ got `@[%a@]`" P.print t
    | _ -> tr_term_aux state t
  and tr_term_aux state t =
    U.map () t
      ~bind:(fun () v -> (), v)
      ~f:(fun () -> tr_term state)

  let tr_ty = tr_term

  (* add binding to state *)
  let add_ state k id =
    Tbl.add state.map k id;
    ID.Tbl.add state.decode id k;
    ()

  (* create new IDs for selectors, testers, etc., add them to [state],
     and return a [encoded_ty] *)
  let ety_of_dataty state ty : encoded_ty =
    let open Stmt in
    assert (ty.ty_vars=[] && U.ty_is_Type ty.ty_type);
    (* add destructors, testers, constructors *)
    let ety_cstors =
      ID.Map.fold
        (fun _ cstor acc ->
           let c_id = cstor.cstor_name in
           add_ state (Cstor c_id) c_id;
           let test = ID.make_f "is_%a" ID.print_name c_id in
           let ty_test = U.ty_arrow (U.const ty.ty_id) U.ty_prop in
           add_ state (Test c_id) test;
           let selectors =
             List.mapi
               (fun i ty_arg ->
                  let s = ID.make_f "select_%a_%d" ID.print_name c_id i in
                  let ty_s = U.ty_arrow (U.const ty.ty_id) ty_arg in
                  add_ state (Select (c_id, i)) s;
                  s, ty_s)
               cstor.cstor_args
           in
           { ecstor_proj=selectors;
             ecstor_test=(test, ty_test);
             ecstor_cstor=(c_id, cstor.cstor_type)} :: acc)
        ty.ty_cstors []
    in
    let ety_card = AT.cardinality_ty_id ~cache:state.at_cache state.env ty.ty_id in
    let res = { ety_id=ty.ty_id; ety_cstors; ety_card; } in
    ID.Tbl.replace state.tys ty.ty_id res;
    res

  let app_id id l = U.app (U.const id) l
  let app_id_fst (id,_) l = app_id id l

  (* declare the new constants *)
  let common_decls etys =
    let mk_decl (id,ty) =
      Stmt.decl ~info:Stmt.info_default ~attrs:[] id ty
    (* cardinality attribute  for this type *)
    and attr_card ety =
      let module C = Cardinality in
      let module Z = C.Z in
      Stmt.Attr_card_hint ety.ety_card
    in
    let tys =
      List.map
        (fun ety ->
           let attrs = [attr_card ety] in
           Stmt.decl ~info:Stmt.info_default ~attrs ety.ety_id U.ty_type)
        etys
    in
    let others =
      CCList.flat_map
        (fun ety ->
           CCList.flat_map
             (fun ec ->
                mk_decl ec.ecstor_cstor
                :: mk_decl ec.ecstor_test
                :: List.map mk_decl ec.ecstor_proj)
             ety.ety_cstors)
        etys
    in
    List.rev_append tys others

  let common_axioms etys =
    let mk_ax f = Stmt.axiom1 ~info:Stmt.info_default f in
    (* axiomatize new constants *)
    CCList.flat_map
      (fun ety ->
         let data_ty = U.const ety.ety_id in
         (* [forall x, not (is_c1 x & is_c2 x)] *)
         let ax_disjointness =
           let x = Var.makef ~ty:data_ty "v_%a" ID.print_name ety.ety_id in
           U.forall x
             (U.and_
                (CCList.diagonal ety.ety_cstors
                 |> List.map
                   (fun (c1,c2) ->
                      U.not_
                        (U.and_
                           [ app_id_fst c1.ecstor_test [U.var x]
                           ; app_id_fst c2.ecstor_test [U.var x]]))))
           |> mk_ax
         (* axiom
            [forall x y,
              (is-c x & is-c y & And_k proj-c-k x = proj-c-k y) => x=y] *)
         and ax_uniqueness =
           List.map
             (fun ec ->
                let x = Var.make ~name:"x" ~ty:data_ty in
                let y = Var.make ~name:"y" ~ty:data_ty in
                U.forall_l [x;y]
                  (U.imply
                     (U.and_
                        ( app_id_fst ec.ecstor_test [U.var x]
                          :: app_id_fst ec.ecstor_test [U.var y]
                          :: List.map
                              (fun (proj,_) ->
                                 U.eq
                                   (U.app_const proj [U.var x])
                                   (U.app_const proj [U.var y]))
                              ec.ecstor_proj))
                     (U.eq (U.var x) (U.var y)))
                |> mk_ax
             )
             ety.ety_cstors
         (* [forall x, Or_c is_c x] *)
         and ax_exhaustiveness =
           let x = Var.makef ~ty:data_ty "v_%a" ID.print_name ety.ety_id in
           U.forall x
             (U.or_
                (List.map
                   (fun ec -> app_id_fst ec.ecstor_test [U.var x])
                   ety.ety_cstors))
           |> mk_ax
         in
         ax_exhaustiveness :: ax_disjointness :: ax_uniqueness
      )
      etys

  (* acyclicity of datatypes:
     - declare a recursive fun [occurs_in : ty -> ty -> prop] such that
       [occurs_in a b] is true iff [a] is a strict subterm of [b].
     - then, assert [forall a. not (occurs_in a a)]
  *)
  let acyclicity_ax state ety : _ Stmt.t list =
    let id = ety.ety_id in
    (* is [ty = id]? *)
    let is_same_ty ty = match T.repr ty with
      | TI.Const id' -> ID.equal id id'
      | _ -> false
    in
    (* [id_c : id -> id -> prop] *)
    let id_c = ID.make_f "occurs_in_%a" ID.print_name id in
    let ty_c = U.ty_arrow_l [U.const id; U.const id] U.ty_prop in
    let def_c = Stmt.mk_defined id_c ty_c in
    ID.Tbl.add state.decode id_c Axiom_rec;
    (* definition:
       [occurs_in x y :=
         exists cstor.
         (y = cstor a1...an && (Or_k (x=a_k || occurs_in x a_k)))]
    *)
    let x = Var.make ~ty:(U.const id) ~name:"x" in
    let y = Var.make ~ty:(U.const id) ~name:"y" in
    let vars = [x;y] in
    let ax_c =
      List.map
        (fun cstor ->
           (* guard: [is_cstor y] *)
           let test = U.app_const (fst cstor.ecstor_test) [U.var y] in
           let subcases =
             CCList.flat_map
               (fun (proj,proj_ty) -> match U.ty_unfold proj_ty with
                  | _, [_], ret when is_same_ty ret ->
                    (* this is a recursive argument, hence a possible case *)
                    [ U.eq (U.var x) (U.app_const proj [U.var y])
                    ; U.app_const id_c [U.var x; U.app_const proj [U.var y]]
                    ]
                  | _ -> [])
               cstor.ecstor_proj
           in
           U.and_ [test; U.or_ subcases])
        ety.ety_cstors
      |> U.or_
    in
    let ax_c =
      U.imply ax_c (U.app_const id_c (List.map U.var vars))
      |> U.forall_l vars
    in
    let def_c =
      Stmt.axiom_spec ~info:Stmt.info_default
        { Stmt.spec_defined=[def_c];
          spec_vars=[];
          spec_axioms=[ax_c];
        }
    in
    (* also assert [forall x y. not (occurs_in x x)] *)
    let ax_no_cycle =
      let a = Var.make ~ty:(U.const id) ~name:"a" in
      U.forall a
        (U.not_ (U.app_const id_c [U.var a; U.var a]))
    in
    [ def_c
    ; Stmt.axiom1 ~info:Stmt.info_default ax_no_cycle
    ]

  (* encode list of data into axioms *)
  let encode_data state l =
    let etys = List.map (ety_of_dataty state) l in
    let decl_l = common_decls etys in
    let ax_l = common_axioms etys in
    let acyclicity_l = CCList.flat_map (acyclicity_ax state) etys in
    decl_l @ acyclicity_l @ ax_l

  (* axiomatization of equality of codatatypes:
     - declare inductive predicate(s) [eq_corec : ty -> ty -> prop] such that
      [eq_corec a b] is true implies [a] and [b] are structurally equal ("bisimilar")
     - assert [forall a b. eq_corec a b => a=b] *)
  let eq_corec_axioms state (etys:encoded_ty list): _ Stmt.t list =
    (* is [ty = id]? *)
    let is_same_ty id ty = match T.repr ty with
      | TI.Const id' -> ID.equal id id'
      | _ -> false
    in
    let l =
      List.map
        (fun ety ->
           let id_ty = ety.ety_id in
           (* [id_c : id -> id -> prop] *)
           let id_c = ID.make_f "eq_corec_%a" ID.print_name id_ty in
           ID.Tbl.add state.decode id_c Axiom_rec;
           id_ty, id_c, ety)
        etys
    in
    (* definition:
       [eq_corec x y :=
         exists cstor.
         (x = cstor a1...an && y = cstor b1...bn &&
            And_k eq_corec a_k b_k)]
    *)
    let def_pred =
      l
      |> List.map
        (fun (id_ty, id_c, ety) ->
           let ty_c = U.ty_arrow_l [U.const id_ty; U.const id_ty] U.ty_prop in
           let def_c = Stmt.mk_defined id_c ty_c in
           let x = Var.make ~ty:(U.const id_ty) ~name:"x" in
           let y = Var.make ~ty:(U.const id_ty) ~name:"y" in
           let vars = [x;y] in
           let clauses =
             ety.ety_cstors
             |> List.map
               (fun cstor ->
                  (* guards: [is_cstor {x,y}] *)
                  let test_x = U.app_const (fst cstor.ecstor_test) [U.var x] in
                  let test_y = U.app_const (fst cstor.ecstor_test) [U.var y] in
                  let subcases =
                    List.map
                      (fun (proj,proj_ty) ->
                         (* how do we decide whether the arguments are equal? *)
                         let mk_eq = match U.ty_unfold proj_ty with
                           | _, [_], ret when is_same_ty id_ty ret ->
                             (fun a b -> U.app_const id_c [a; b])
                           | _ -> U.eq
                         in
                         mk_eq (U.app_const proj [U.var x]) (U.app_const proj [U.var y])
                      )
                      cstor.ecstor_proj
                  in
                  let guard = U.and_ (test_x :: test_y :: subcases) in
                  let concl = U.app_const id_c [U.var x; U.var y] in
                  {Stmt.
                    clause_vars=vars;
                    clause_concl=concl;
                    clause_guard=Some guard;
                  })
           in
           {Stmt.
             pred_tyvars=[];
             pred_defined=def_c;
             pred_clauses=clauses}
        )
      |> Stmt.copred ~info:Stmt.info_default ~wf:`Not_wf
    in
    (* also assert [forall x y. eq_corec_ty x y => x=y] for each type *)
    let ax_eq =
      List.map
        (fun (id_ty,id_c,_) ->
           let x = Var.make ~ty:(U.const id_ty) ~name:"x" in
           let y = Var.make ~ty:(U.const id_ty) ~name:"y" in
           U.forall_l [x;y]
             (U.imply
                (U.app_const id_c [U.var x; U.var y])
                (U.eq (U.var x) (U.var y)))
           |> Stmt.axiom1 ~info:Stmt.info_default
        )
        l
    in
    def_pred :: ax_eq

  (* encode list of codata into axioms *)
  let encode_codata state l =
    let etys = List.map (ety_of_dataty state) l in
    let decl_l = common_decls etys in
    let ax_l = common_axioms etys in
    (* definition of coinductive equality *)
    let eq_axiom_l = eq_corec_axioms state etys in
    decl_l @ eq_axiom_l @ ax_l

  let encode_stmt state stmt = match Stmt.view stmt, mode with
    | Stmt.TyDef (`Codata, _), M_data
    | Stmt.Pred _, M_data -> assert false (* invariant broken *)
    | Stmt.TyDef (`Codata, l), M_codata ->
      Utils.debugf ~section 2 "@[<2>encode codata@ `@[%a@]`@]"
        (fun k->k PStmt.print_tydefs (`Codata, l));
      encode_codata state l
    | Stmt.TyDef (`Data, l), M_data ->
      Utils.debugf ~section 2 "@[<2>encode data@ `@[%a@]`@]"
        (fun k->k PStmt.print_tydefs (`Data, l));
      encode_data state l
    | _ ->
      let stmt =
        Stmt.map stmt ~term:(tr_term state) ~ty:(tr_ty state)
      in
      [stmt]

  let transform_pb pb =
    let env = Problem.env pb in
    let state = create_state ~env () in
    let pb' =
      Problem.flat_map_statements pb
        ~f:(encode_stmt state)
    in
    pb', state

  (** {2 Decoding} *)

  type fun_def = T.t Var.t list * (T.t, T.t) Model.DT.t * Model.symbol_kind

  module IntMap = CCMap.Make(CCInt)

  (* temporary structure used for decoding terms *)
  type decoding = {
    dec_constants: encoded_ty ID.Map.t;
    (* set of constants whose type is a (co)data, and therefore
       that are to be removed by decoding.
       Each constant maps to the corresponding {!encoded_ty} *)
    dec_test: fun_def ID.Map.t;
    (* tester -> definition of tester *)
    dec_select: fun_def IntMap.t ID.Map.t;
    (* cstor, definition of selectors *)
  }

  let decoding_empty = {
    dec_constants=ID.Map.empty;
    dec_test=ID.Map.empty;
    dec_select=ID.Map.empty
  }

  (* build a {!decoding} structure from the model *)
  let build_decoding state m =
    Model.fold
      decoding_empty
      m
      ~finite_types:(fun dec (ty,dom) ->
        match T.repr ty with
          | TI.Const id when ID.Tbl.mem state.tys id ->
            (* [id] is a (co)data, and we know its encoding *)
            let ety = ID.Tbl.find state.tys id in
            List.fold_left
              (fun dec c ->
                 let dec_constants = ID.Map.add c ety dec.dec_constants in
                 {dec with dec_constants;})
              dec dom
          | _ -> dec)
      ~funs:(fun dec (t,vars,dt,k) -> match T.repr t with
        | TI.Const id ->
          begin match ID.Tbl.get state.decode id with
            | None -> dec
            | Some (Test _) ->
              {dec with dec_test=ID.Map.add id (vars,dt,k) dec.dec_test}
            | Some (Select (c,i)) ->
              let m = ID.Map.get_or ~or_:IntMap.empty c dec.dec_select in
              let m = IntMap.add i (vars,dt,k) m in
              {dec with dec_select=ID.Map.add c m dec.dec_select}
            | Some (Cstor _ | Axiom_rec) -> dec
          end
        | _ -> dec)

  module DTU = Model.DT_util(T)

  let eval_fundef (f:fun_def) (arg:T.t) : T.t =
    let vars, dt, _ = f in
    match vars with
      | [] -> assert false
      | [v] ->
        let subst = Var.Subst.singleton v arg in
        DTU.eval ~subst dt
      | v :: other_vars ->
        (* 'tis a function, mate! *)
        let subst = Var.Subst.singleton v arg in
        let subst, other_vars' = CCList.fold_map U.rename_var subst other_vars in
        let body = DTU.eval ~subst dt in
        U.fun_l other_vars' body

  (* evaluate a boolean function def *)
  let eval_bool_fundef (f:fun_def) (arg:T.t) : bool option =
    let _, _, k = f in
    assert (k = Model.Symbol_prop);
    let res = eval_fundef f arg in
    match T.repr res with
      | TI.Builtin `True -> Some true
      | TI.Builtin `False -> Some false
      | _ -> None

  let find_test_ dec id =
    try ID.Map.find id dec.dec_test
    with Not_found ->
      errorf "could not find, in model,@ the value for tester `%a`" ID.print id

  let find_select_ dec c i =
    try
      let map = ID.Map.find c dec.dec_select in
      IntMap.find i map
    with Not_found ->
      errorf "could not find, in model,@ the value for %d-th selector of `%a`"
        i ID.print c

  (* we are under this cstor, for which the variable [msc_var] was provisioned.
     If we use [msc_var] we should set [msc_used] to true so that the
     binder is effectively produced *)
  type mu_stack_cell = {
    msc_cstor: ID.t;
    msc_var: ty Var.t;
    mutable msc_used: bool;
  }

  type mu_stack = mu_stack_cell list

  (* decode a term, recursively, replacing constants of uninterpreted
     domains by their value in the model *)
  let decode_term dec t =
    let find_in_stack stack id : mu_stack_cell option =
      CCList.find_pred
        (fun msc -> ID.equal msc.msc_cstor id)
        stack
    in
    (* @param stack the list of cstors we are under *)
    let rec aux (stack:mu_stack) t = match T.repr t with
      | TI.Const id ->
        begin match find_in_stack stack id, ID.Map.get id dec.dec_constants with
          | None, None -> t
          | Some msc, _ ->
            (* we are already decoding [id] deeper in the stack, use the
               appropriate variable and signal that we are using it *)
            msc.msc_used <- true;
            U.var msc.msc_var
          | None, Some ety ->
            (* [t] is something like [list_5], and we need to find which
                   constructor it actually is *)
            Utils.debugf ~section 5
              "@[<2>constant `%a`@ corresponds to (co)data `%a`@]"
              (fun k->k ID.print id ID.print ety.ety_id);
            (* find which constructor corresponds to [t] *)
            let ecstor =
              try
                CCList.find_pred_exn
                  (fun ecstor ->
                     let fundef = find_test_ dec (fst ecstor.ecstor_test) in
                     match eval_bool_fundef fundef t with
                       | None ->
                         errorf "cannot evaluate whether `%a`@ \
                                 starts with constructor `%a`"
                           P.print t ID.print (fst ecstor.ecstor_cstor)
                       | Some b -> b)
                  ety.ety_cstors
              with Not_found ->
                errorf "no constructor corresponds to `%a`" P.print t
            in
            (* var in case we need to bind *)
            let msc = {
              msc_cstor=id;
              msc_var=
                Var.makef "self_%d" (List.length stack)
                  ~ty:(U.ty_const ety.ety_id);
              msc_used=false;
            } in
            (* evaluate the arguments to this constructor *)
            let cstor = fst ecstor.ecstor_cstor in
            let args =
              List.mapi
                (fun i _ ->
                   let fundef = find_select_ dec cstor i in
                   let arg = eval_fundef fundef t in
                   aux (msc::stack) arg)
                ecstor.ecstor_proj
            in
            let t' = U.app_const cstor args in
            (* add mu-binder if needed *)
            let t' = if msc.msc_used then U.mu msc.msc_var t' else t' in
            Utils.debugf ~section 5 "@[<2>term `@[%a@]`@ is decoded into `@[%a@]`@]"
              (fun k->k P.print t P.print t');
            t'
        end
      | _ ->
        U.map () t
          ~bind:(fun () v -> (), v)
          ~f:(fun () t -> aux stack t)
    in
    aux [] t

  (* remove model of constructors/inductive types *)
  let decode_model state (m:(_,_) Model.t) : (_,_) Model.t =
    let dec = build_decoding state m in
    let tr_term t = decode_term dec t in
    Model.filter_map m
      ~finite_types:(fun ((ty,_) as tup) ->
        match T.repr ty with
          | TI.Const id when ID.Tbl.mem state.tys id ->
            None (* drop (co)data domains from model *)
          | _ -> Some tup)
      ~constants:(fun (t,u,k) ->
        match T.repr t with
          | TI.Const id when ID.Tbl.mem state.decode id ->
            None (* drop the domain constants *)
          | _ ->
            let t = tr_term t in
            let u = tr_term u in
            Some (t,u,k))
      ~funs:(fun (f,vars,dt,k) -> match T.repr f with
        | TI.Const id when ID.Tbl.mem state.decode id -> None
        | _ ->
          let f = tr_term f in
          let dt = Model.DT.map dt ~term:tr_term ~ty:tr_term in
          Some (f,vars,dt,k))

  (** {2 Pipeline} *)

  module F = Transform.Features

  let input_spec : F.t = match mode with
    | M_data ->
      F.(of_list
          [Ty, Mono; Match, Absent; Data, Present;
           Eqn, Eqn_single; Codata, Absent; Ind_preds, Absent])
    | M_codata ->
      F.(of_list [Ty, Mono; Match, Absent; Codata, Present; Eqn, Eqn_single])

  let map_spec : F.t -> F.t = match mode with
    | M_data -> F.(update Data Absent)
    | M_codata ->
      F.(update_l [Codata, Absent; Data, Present; Ind_preds, Present])

  let pipe_with ?on_decoded ~decode ~print ~check =
    let on_encoded =
      Utils.singleton_if check ()
        ~f:(fun () ->
          let module C = TypeCheck.Make(T) in
          C.empty () |> C.check_problem)
      @
      Utils.singleton_if print ()
        ~f:(fun () ->
          let module Ppb = Problem.Print(P)(P) in
          Format.printf "@[<v2>@{<Yellow>after %s@}: %a@]@." name Ppb.print)
    in
    Transform.make
      ~name
      ~on_encoded
      ?on_decoded
      ~input_spec
      ~map_spec
      ~encode:transform_pb
      ~decode
      ()

  let pipe ~print ~check =
    let on_decoded = if print
      then
        [Format.printf "@[<2>@{<Yellow>res after %s@}:@ %a@]@."
           name (Problem.Res.print P.print' P.print)]
      else []
    in
    let decode state = Problem.Res.map_m ~f:(decode_model state) in
    pipe_with ~on_decoded ~check ~decode ~print
end

module Data = Make(struct let mode = M_data end)
module Codata = Make(struct let mode = M_codata end)
