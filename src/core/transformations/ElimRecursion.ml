
(* This file is free software, part of nunchaku. See file "license" for more details. *)

module ID = ID
module Var = Var
module TI = TermInner
module TyI = TypeMono
module Stmt = Statement
module Sig = Signature

type id = ID.t

let name = "rec_elim"

let section = Utils.Section.make name

type inv1 = <ty:[`Mono]; eqn:[`App]; ind_preds:[`Absent]>
type inv2 = <ty:[`Mono]; eqn:[`Absent]; ind_preds:[`Absent]>

exception Attr_abs_type of ID.t

exception Attr_abs_projection of ID.t * int

exception Attr_is_handle_cstor

exception Attr_app_val

exception Attr_proto_val of ID.t * int

let fpf = Format.fprintf
let spf = CCFormat.sprintf

let () = Printexc.register_printer
  (function
    | Attr_abs_type fun_id -> Some (spf "abs_type_of %a" ID.print fun_id)
    | Attr_abs_projection (ty_id,i) -> Some (spf "abs_proj_%d %a" i ID.print ty_id)
    | Attr_app_val -> Some "app_symbol"
    | Attr_is_handle_cstor -> Some "handle_type"
    | Attr_proto_val (id, n) -> Some (spf "proto_%d_of_%a" n ID.print id)
    | _ -> None)

module Make(T : TI.S) = struct
  module U = TI.Util(T)
  module P = TI.Print(T)
  module PStmt = Stmt.Print(P)(P)
  module Subst = Var.Subst
  module TyM = TypeMono.Make(T)

  type term = T.t
  type ty = T.t

  (* how to encode a single recursive function/predicate *)
  type fun_encoding = {
    fun_encoded_fun: id;
      (* name of function encoded this way *)
    fun_abstract_ty: ty;
      (* type of abstract values for the function *)
    fun_abstract_ty_id: id;
      (* symbol corresponding to [fun_abstract_ty] *)
    fun_concretization: (int * id * ty) list;
      (* for each parameter, concretization function, as an association list *)
  }

  type decode_state = {
    approx_fun : fun_encoding ID.Tbl.t;
      (* concretization_fun -> function it is used to encode *)
    encoded_fun : fun_encoding ID.Tbl.t;
      (* recursive function -> its encoding *)
    abstract_ty : fun_encoding ID.Tbl.t;
      (* set of abstraction types *)
  }

  (** {6 Encoding} *)

  (* state used for the translation *)
  type state = {
    decode: decode_state;
      (* for decoding purpose *)
    mutable sigma: ty Sig.t;
      (* signature *)
  }

  let create_state() = {
    decode={
      approx_fun=ID.Tbl.create 16;
      encoded_fun=ID.Tbl.create 16;
      abstract_ty=ID.Tbl.create 16;
    };
    sigma=Sig.empty;
  }

  exception TranslationFailed of term * string
  (* not supposed to escape *)

  exception DecodingFailed of T.t option * string

  let fail_tr_ t msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (TranslationFailed (t,msg)))

  let fail_decode_ ?term:t msg =
    Utils.exn_ksprintf msg ~f:(fun msg -> raise (DecodingFailed (t,msg)))

  let () = Printexc.register_printer
    (function
      | TranslationFailed (t,msg) ->
          Some (spf "@[<2>translation of `@[%a@]` failed:@ %s@]" P.print t msg)
      | DecodingFailed (None, msg) ->
          Some (spf "@[<2>decoding failed:@ %s@]" msg)
      | DecodingFailed (Some t, msg) ->
          Some (spf "@[<2>decoding of `@[%a@]` failed:@ %s@]" P.print t msg)
      | _ -> None)

  (* list of argument types that (monomorphic) type expects *)
  let rec ty_args_ (ty:term) = match TyM.repr ty with
    | TyI.Builtin _ | TyI.Const _ | TyI.App (_,_) -> []
    | TyI.Arrow (a,ty') -> a :: ty_args_ ty'

  (* sort [fun_encoding.fun_concretization] *)
  let sort_concretization = List.sort (fun (i,_,_)(j,_,_) -> CCInt.compare i j)

  (*
    - apply substitution eagerly (build it when we enter `forall_f x. f x = t`)
    - when we meet `f t1...tn`:
        - add 1 constraint `exists alpha. And_i (proj_i alpha = t_i)`;
        - keep same term
  *)

  (* if [f] is a recursively defined function that is being eliminated,
      then return [Some def_of_f] *)
  let as_defined_ ~state f = match T.repr f with
    | TI.Const id ->
        begin try
          Some (id, ID.Tbl.find state.decode.encoded_fun id)
        with Not_found -> None
        end
    | _ -> None

  (* translate term/formula recursively into a new (guarded) term. *)
  let rec tr_term_rec_ ~state subst t =
    match T.repr t with
    | TI.Const _ -> t
    | TI.Var v ->
        (* substitute if needed; no side-condition *)
        begin match Subst.find ~subst v with
          | None -> t
          | Some t' -> t'
        end
    | TI.App (f,l) ->
        begin match as_defined_ ~state f with
          | Some (id, fundef) ->
              (* [f] is a recursive function we are encoding *)
              if List.length l <> List.length fundef.fun_concretization
                then fail_tr_ t
                  "defined function %a is partially applied (%d arguments, expected %d)"
                  ID.print id (List.length l) (List.length fundef.fun_concretization);
              (* existential variable *)
              let alpha = Var.make ~name:"a" ~ty:fundef.fun_abstract_ty in
              let eqns = ref [] in
              let l' = List.map2
                (fun arg (_i, proj,_ty_proj) ->
                  let arg' = tr_term_rec_ ~state subst arg in
                  let eqn = U.eq arg' (U.app (U.const proj) [U.var alpha]) in
                  eqns := eqn :: !eqns;
                  arg')
                l
                fundef.fun_concretization
              in
              let cond = U.exists alpha (U.and_ !eqns) in
              U.asserting (U.app f l') [cond]
          | None ->
              (* generic treatment *)
              tr_term_rec_' ~state subst t
        end
    | TI.Builtin (`True | `False
        | `And | `Or | `Not | `Imply | `DataSelect _ | `DataTest _) ->
          t (* partially applied, or constant *)
    | TI.Builtin (`Undefined _ as b) ->
        U.builtin (TI.Builtin.map b ~f:(tr_term_rec_ ~state subst))
    | TI.Builtin (`Guard (t, g)) ->
        let t = tr_term_rec_ ~state subst t in
        let g' = TI.Builtin.map_guard (tr_term_rec_ ~state subst) g in
        U.guard t g'
    | TI.Bind (`Fun,_,_) -> fail_tr_ t "translation of λ impossible"
    | TI.Builtin (`Equiv _ | `Eq _ | `Ite _)
    | TI.Bind ((`Forall | `Exists | `Mu), _, _)
    | TI.Match _
    | TI.Let _ ->
        tr_term_rec_' ~state subst t
    | TI.TyBuiltin _
    | TI.TyArrow (_,_) -> t
    | TI.Bind (`TyForall, _, _)
    | TI.TyMeta _ -> assert false

  and tr_term_rec_' ~state subst t =
    U.map subst t
      ~f:(tr_term_rec_ ~state)
      ~bind:(fun subst v ->
        (* rename [v] *)
        let v' = Var.fresh_copy v in
        let subst = Subst.add ~subst v (U.var v') in
        subst, v')

  let tr_term ~state subst t =
    Utils.debugf ~section 4
      "@[<2>convert toplevel term@ `@[%a@]`@]" (fun k -> k P.print t);
    tr_term_rec_ ~state subst t

  (* translate a top-level formula *)
  let tr_form ~state t =
    tr_term ~state Subst.empty t

  (* translate equation [eqn], which is defining the function
     corresponding to [fun_encoding].
     It returns an axiom instead. *)
  let tr_eqns ~state ~fun_encoding ty eqn =
    let Stmt.Eqn_single (vars,rhs) = eqn in
    let id = fun_encoding.fun_encoded_fun in
    (* quantify over abstract variable now *)
    let alpha = Var.make ~ty:fun_encoding.fun_abstract_ty ~name:"a" in
    (* replace each [x_i] by [proj_i var] *)
    assert (List.length vars = List.length fun_encoding.fun_concretization);
    let args' =
      fun_encoding.fun_concretization
      |> sort_concretization
      |> List.map (fun (_,proj,_) -> U.app (U.const proj) [U.var alpha])
    in
    let subst = Subst.add_list ~subst:Subst.empty vars args' in
    (* convert right-hand side and add its side conditions *)
    let lhs = U.app (U.const fun_encoding.fun_encoded_fun) args' in
    let rhs' = tr_term ~state subst rhs in
    (* how to connect [lhs] and [rhs]? *)
    let connect lhs rhs = match ID.polarity id with
      | Polarity.Pos -> U.imply lhs rhs
      | Polarity.Neg -> U.imply rhs lhs
      | Polarity.NoPol ->
          if U.ty_returns_Prop ty
          then U.equiv lhs rhs
          else U.eq lhs rhs
    in
    U.forall alpha (connect lhs rhs')

  (* transform the recursive definition (mostly, its equations) *)
  let tr_rec_def ~state ~fun_encoding def =
    tr_eqns ~state ~fun_encoding
      def.Stmt.rec_defined.Stmt.defined_ty def.Stmt.rec_eqns

  (* add an [encoding] to the state *)
  let add_encoding ~state fun_encoding =
    ID.Tbl.add state.decode.encoded_fun fun_encoding.fun_encoded_fun fun_encoding;
    ID.Tbl.add state.decode.abstract_ty fun_encoding.fun_abstract_ty_id fun_encoding;
    List.iter
      (fun (_,proj,_ty_proj) ->
        ID.Tbl.add state.decode.approx_fun proj fun_encoding)
      fun_encoding.fun_concretization;
    ()

  (* TODO: before creating new projectors, check whether some already
    exist (thanks to attributes, etc.) *)

  let tr_rec_defs ~info ~state l =
    (* transform each axiom, considering case_head as rec. defined *)
    let new_stmts = ref [] in
    let add_stmt = CCList.Ref.push new_stmts in
    (* first, build and register an encoding for each defined function *)
    List.iter
      (fun def ->
        let id = def.Stmt.rec_defined.Stmt.defined_head in
        (* declare abstract type + projectors first *)
        let name = "G_" ^ ID.to_string_slug id in
        let abs_type_id = ID.make name in
        let abs_type = U.ty_const abs_type_id in
        let ty = Sig.find_exn ~sigma:state.sigma id in
        (* projection function: one per argument. It has
          type  [abs_type -> type of arg] *)
        let projectors =
          List.mapi
            (fun i ty_arg ->
              let id' = ID.make (Printf.sprintf "proj_%s_%d" name i) in
              let ty' = U.ty_arrow abs_type ty_arg in
              i, id', ty')
            (ty_args_ ty)
        in
        let fun_encoding = {
          fun_encoded_fun=id;
          fun_abstract_ty_id=abs_type_id;
          fun_abstract_ty=abs_type;
          fun_concretization=projectors;
        } in
        add_encoding ~state fun_encoding;
        (* declare abstract type + projectors + the function
           NOTE: we need to declare the function because it is no longer
            defined, only axiomatized *)
        add_stmt
          (Stmt.ty_decl ~info:Stmt.info_default abs_type_id U.ty_type
             ~attrs:[Stmt.Decl_attr_exn (Attr_abs_type id)]);
        add_stmt
          (Stmt.decl ~info:Stmt.info_default ~attrs:[]
            id def.Stmt.rec_defined.Stmt.defined_ty);
        List.iter
          (fun (n,proj,ty_proj) ->
            add_stmt
              (Stmt.decl ~info:Stmt.info_default proj ty_proj
                 ~attrs:[Stmt.Decl_attr_exn (Attr_abs_projection (abs_type_id, n))]))
          fun_encoding.fun_concretization;
      )
      l;
    (* then translate each definition *)
    let l' = List.map
      (fun def ->
        try
          let id = def.Stmt.rec_defined.Stmt.defined_head in
          let fun_encoding = ID.Tbl.find state.decode.encoded_fun id in
          tr_rec_def ~state ~fun_encoding def
        with TranslationFailed (t, msg) as e ->
          (* could not translate, keep old definition *)
          Utils.debugf ~section 1
            "@[<2>recursion elimination in@ @[%a@]@ \
              failed on subterm @[%a@]:@ %s@]"
              (fun k -> k PStmt.print (Stmt.axiom_rec ~info l) P.print t msg);
          raise e)
      l
    in
    (* add new statements (type declarations) before l' *)
    List.rev_append !new_stmts [Stmt.axiom ~info l']

  (* translate a statement *)
  let tr_statement ~state st =
    (* update signature *)
    state.sigma <- Sig.add_statement ~sigma:state.sigma st;
    let info = Stmt.info st in
    match Stmt.view st with
    | Stmt.Decl (id,k,l,attrs) ->
        [Stmt.mk_decl ~info ~attrs id k l] (* no type declaration changes *)
    | Stmt.TyDef (k,l) -> [Stmt.mk_ty_def ~info k l] (* no (co) data changes *)
    | Stmt.Pred _ -> assert false (* typing: should be absent *)
    | Stmt.Axiom l ->
        begin match l with
        | Stmt.Axiom_rec l ->
            tr_rec_defs ~info ~state l
        | Stmt.Axiom_spec spec ->
            let spec' =
              Stmt.map_spec_defs ~term:(tr_form ~state) ~ty:CCFun.id spec
            in
            [Stmt.axiom_spec ~info spec']
        | Stmt.Axiom_std l ->
            let l = List.map
              (fun t -> tr_form ~state t)
              l in
            [Stmt.axiom ~info l]
        end
    | Stmt.Copy c -> [Stmt.copy ~info c]
    | Stmt.Goal g ->
        [Stmt.goal ~info (tr_form ~state g)]

  (* find whether attributes contain some [abs_type_of id] *)
  let on_handle_ty_ ~f =
    List.iter
      (function
        | Stmt.Decl_attr_exn (Attr_abs_type id) -> f id
        | _ -> ())

  (* find whether attributes contain some [abs_proj_n id] *)
  let on_proj_ ~f =
    List.iter
      (function
        | Stmt.Decl_attr_exn (Attr_abs_projection (ty_id,n)) -> f ty_id n
        | _ -> ())

  let populate_state ~state stmts =
    (* table for partially filled [fun_encoding]s *)
    let partial = ID.Tbl.create 32 in
    CCVector.iter
      (fun st -> match Stmt.view st with
        | Stmt.Decl (id, _decl, ty, attrs) ->
            on_handle_ty_ attrs
              ~f:(fun fun_id ->
                (* create a fun_encoding for [fun_id] (whose handle type is id) *)
                let fun_encoding = {
                  fun_encoded_fun=fun_id;
                    fun_abstract_ty_id=id;
                    fun_abstract_ty=U.ty_const id;
                    fun_concretization=[];
                } in
                ID.Tbl.add partial id fun_encoding);
            on_proj_ attrs
              ~f:(fun ty_id n ->
                  (* id is the n-th projection of the handle ty_id *)
                  let fun_ = ID.Tbl.find partial ty_id in
                  let ty_proj = ty in
                  let fun_ =
                    { fun_ with
                      fun_concretization=(n,id,ty_proj) :: fun_.fun_concretization; }
                  in
                  ID.Tbl.replace partial ty_id fun_)
        | _ -> ())
      stmts;
    (* assume all the declarations are now complete, and add them to [state] *)
    ID.Tbl.iter
      (fun _ fun_encoding -> add_encoding ~state fun_encoding)
      partial

  let elim_recursion pb =
    let state = create_state() in
    populate_state ~state (Problem.statements pb);
    let pb' = Problem.flat_map_statements ~f:(tr_statement ~state) pb in
    pb', state.decode

  (** {6 Decoding}

    We expect to get back a model where the encoded functions (and their
    projections) are decision trees over finite domains.

    To make things more readable for the user, we drop the projections
    from the model, and limit the encoded functions to the
    domain where their projections were defined (the domain on which it
    is not garbage) *)

  type finite_domain = {
    dom_fun: fun_encoding;
      (* function *)
    dom_dom: ID.t list;
      (* abstract domain *)
    mutable dom_args: term list ID.Map.t;
      (* for each abstract value in the approximation type, the list of
         concrete arguments it corresponds to *)
  }

  type finite_domains = finite_domain ID.Tbl.t
  (* map abstracted function -> its domain *)

  let pp_domain out d =
    let pp_tuple out (id,l) =
      fpf out "%a → (@[%a@])" ID.print id
        (CCFormat.list ~start:"" ~stop:"" P.print) l
    in
    fpf out "[@[<v2>`%a`:@ %a@]]"
      ID.print d.dom_fun.fun_encoded_fun
      (CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_tuple) (ID.Map.to_seq d.dom_args)

  type proj_fun = {
    proj_var: T.t Var.t;
      (* argument to the projection function *)

    proj_tree: (T.t, T.t) Model.decision_tree;
      (* decision tree for the variable *)
  }

  module DT_util = Model.DT_util(T)

  (*
     - gather definitions of projections
     - gather domains of abstract types
  *)
  let pass1_ ~state m =
    let projs : proj_fun ID.Tbl.t = ID.Tbl.create 16 in
    let doms  : finite_domain ID.Tbl.t = ID.Tbl.create 16 in
    Model.iter m
      ~constants:(fun (t,_,_) -> match T.repr t with
        | TI.Const id ->
            (* a function should not be modeled by a constant *)
            assert (not (ID.Tbl.mem state.approx_fun id));
        | _ -> ())
      ~funs:(fun (t,vars,body,_) -> match T.repr t, vars with
        | TI.Const id, [v] ->
            (* register the model for this approximated function *)
            if ID.Tbl.mem state.approx_fun id
            then ID.Tbl.add projs id {proj_var=v; proj_tree=body; }
        | _, _ -> ())
      ~finite_types:(fun (ty,dom) -> match T.repr ty with
        | TI.Const id ->
            begin try
              let dom_fun = ID.Tbl.find state.abstract_ty id in
              let dom = {dom_fun; dom_dom=dom; dom_args=ID.Map.empty; } in
              ID.Tbl.add doms dom_fun.fun_encoded_fun dom
            with Not_found -> ()
            end
        | _ -> ());
      projs, doms

  (* compute map `abstract type -> set of tuples by projection`.
   Update doms. *)
  let pass2_ projs (doms:finite_domains) =
    ID.Tbl.iter
      (fun _ fdom ->
        List.iter
          (fun val_id ->
            let args =
              fdom.dom_fun.fun_concretization
              |> sort_concretization
              |> List.map
                (fun (_,f_id,_) ->
                  let proj =
                    try ID.Tbl.find projs f_id
                    with Not_found ->
                      fail_decode_ "could not find value of projection function %a on %a"
                        ID.print f_id ID.print val_id
                  in
                  let subst = Var.Subst.singleton proj.proj_var (U.const val_id) in
                  DT_util.eval ~subst proj.proj_tree)
            in
            fdom.dom_args <- ID.Map.add val_id args fdom.dom_args)
          fdom.dom_dom)
      doms;
    ()

  (* translate definitions of rec. functions based on
      the map (only keep in the domain, tuples that are obtained by
      projections, the rest is junk)
  *)
  let pass3_ ~state doms m =
    (* decode a function. *)
    let decode_fun_ f_id dom vars body =
      let arity = List.length dom.dom_fun.fun_concretization in
      if List.length vars <> arity
        then fail_decode_
          ~term:(U.fun_l vars (DT_util.to_term body))
          "expected a function of %d arguments" arity;
      (* compute value of the function applied to [tup] *)
      let apply_to tup =
        let subst = Subst.add_list ~subst:Subst.empty vars tup in
        DT_util.eval ~subst body
      in
      (* set of tuples on which the function is defined *)
      let dom_tuples = ID.Map.to_list dom.dom_args |> List.map snd in
        (* default case: undefined
          TODO: if initial domain was finite, this might be unecessary,
            because CVC4 could model the whole domain? *)
      let default = U.undefined_ (U.app (U.const f_id) (List.map U.var vars)) in
      let new_body =
        List.map
          (fun tup ->
            let test = List.combine vars tup in
            let then_ = apply_to tup in
            test, then_)
          dom_tuples
      in
      Model.DT.test new_body ~else_:default
    in
    (* now remove projections and filter recursion functions's values *)
    Model.filter_map m
      ~constants:(fun (t,u,k) -> match T.repr t with
        | TI.Const id when ID.Tbl.mem state.approx_fun id ->
            None (* drop approximation functions *)
        | _ -> Some (t,u,k))
      ~funs:(fun (t,vars,body,k) -> match T.repr t with
        | TI.Const id when ID.Tbl.mem state.approx_fun id ->
            None (* drop approximation functions *)
        | TI.Const f_id when ID.Tbl.mem state.encoded_fun f_id ->
            (* remove junk from the definition of [t] *)
            let body' = decode_fun_ f_id (ID.Tbl.find doms f_id) vars body in
            Utils.debugf ~section 3
              "@[<hv2>decoding of recursive fun @[%a %a@] :=@ `@[%a@]`@ is `@[%a@]`@]"
              (fun k->k ID.print f_id (CCFormat.list Var.print_full) vars
              (Model.DT.print P.print) body (Model.DT.print P.print) body');
            Some (t, vars, body',k)
        | _ ->
            (* keep *)
            Some (t,vars,body,k))
      ~finite_types:(fun ((ty,_) as pair) -> match T.repr ty with
        | TI.Const id when ID.Tbl.mem state.abstract_ty id ->
            None (* remove abstraction types *)
        | _ -> Some pair)

  let decode_model ~state m =
    Utils.debugf ~section 3 "@[<2>decode model:@ @[%a@]@]"
      (fun k->k (Model.print P.print P.print) m);
    let projs, domains = pass1_ ~state m in
    pass2_ projs domains;
    Utils.debugf ~section 2 "@[<2>domains:@ @[%a@]@]"
      (fun k->k (CCFormat.seq ~start:"" ~stop:"" pp_domain) (ID.Tbl.values domains));
    let m = pass3_ ~state domains m in
    Utils.debugf ~section 3 "@[<2>model after decoding:@ @[%a@]@]"
      (fun k->k (Model.print P.print P.print) m);
    m

  (** {6 Pipe} *)

  let pipe_with ~decode ~print =
    let on_encoded = if print
      then
        let module PPb = Problem.Print(P)(P) in
        [Format.printf "@[<v2>@{<Yellow>after elimination of recursion@}: %a@]@." PPb.print]
      else []
    in
    Transform.make1
      ~on_encoded
      ~name
      ~encode:(fun p ->
        let p, state = elim_recursion p in
        p, state
      )
      ~decode
      ()

  let pipe ~print =
    let decode state m = decode_model ~state m in
    pipe_with ~print ~decode
end
