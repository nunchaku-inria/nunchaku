(* This file is free software, part of nunchaku. See file "license" for more details. *)

module Var = Var
module ID = ID
module TI = TermInner

type id = ID.t
type 'a var = 'a Var.t
type loc = Location.t
type 'a printer = Format.formatter -> 'a -> unit

type decl =
  | Decl_type
  | Decl_fun
  | Decl_prop

type 'ty defined = {
  defined_head: id; (* symbol being defined *)
  defined_ty: 'ty; (* type of the head symbol *)
}

type (+'t, +'ty, 'kind) equations =
  | Eqn_nested :
      ('ty var list (* universally quantified vars *)
      * 't list (* arguments (patterns) to the defined term *)
      * 't  (* right-hand side of equation *)
      * 't list (* additional conditions *)
      ) list
      -> ('t, 'ty, <eqn:[`Nested]; ty:_; ..>) equations
  | Eqn_single :
      'ty var list (* function arguments *)
      *  't (* RHS *)
      -> ('t, 'ty, <eqn:[<`Single | `App]; ty:_; ..>) equations
  | Eqn_app :
      (ID.t list (* application symbols *)
      * 'ty var list (* quantified vars *)
      * 't (* LHS of equation *)
      * 't (* RHS of equation *)
      ) -> ('t, 'ty, <eqn:[`App]; ty:[`Mono]; ..>) equations

type (+'t,+'ty,'kind) rec_def = {
  rec_defined: 'ty defined;
  rec_kind: decl;
  rec_vars: 'ty var list; (* type variables in definitions *)
  rec_eqns: ('t, 'ty,'kind) equations; (* list of equations defining the term *)
}

type (+'t, +'ty,'kind) rec_defs = ('t, 'ty,'kind) rec_def list

type (+'t, +'ty) spec_defs = {
  spec_vars: 'ty var list; (* type variables used by defined terms *)
  spec_defined: 'ty defined list;  (* terms being specified together *)
  spec_axioms: 't list;  (* free-form axioms *)
}

(** A type constructor: name + type of arguments *)
type +'ty ty_constructor = {
  cstor_name: id; (** Name *)
  cstor_args: 'ty list; (** type arguments *)
  cstor_type: 'ty; (** type of the constructor (shortcut) *)
}

(** A (co)inductive type. The type variables [ty_vars] occur freely in
    the constructors' types. *)
type +'ty tydef = {
  ty_id : id;
  ty_vars : 'ty Var.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor ID.Map.t;
}

(** Mutual definitions of several types *)
type +'ty mutual_types = 'ty tydef list

(** Flavour of axiom *)
type (+'t,+'ty,'kind) axiom =
  | Axiom_std of 't list
    (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
    (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty,'kind) rec_defs
    (** Axioms are part of an admissible (partial) definition *)

type (+'t, +'ty) pred_clause_cell = {
  clause_vars: 'ty var list; (* universally quantified vars *)
  clause_guard: 't option;
  clause_concl: 't;
}

type (+_, +_, _) pred_clause =
  | Pred_clause :
    ('t, 'ty) pred_clause_cell ->
    ('t, 'ty, <ind_preds:[`Present];..>) pred_clause

type ('t, 'ty, 'inv) pred_def = {
  pred_defined: 'ty defined;
  pred_tyvars: 'ty var list;
  pred_clauses: ('t, 'ty, 'inv) pred_clause list;
}

type (+'t, +'ty) copy = {
  copy_id: ID.t; (* new name *)
  copy_vars: 'ty Var.t list; (* list of type variables *)
  copy_ty: 'ty;  (* type of [copy_id], of the form [type -> type -> ... -> type] *)
  copy_of: 'ty; (* [id vars] is a copy of [of_]. Set of variables = vars *)
  copy_abstract: ID.t; (* [of -> id vars] *)
  copy_abstract_ty: 'ty;
  copy_concretize: ID.t; (* [id vars -> of] *)
  copy_concretize_ty: 'ty;
  copy_pred: 't option; (* invariant (prop) *)
}

(** Attribute on declarations *)
type decl_attr =
  | Decl_attr_card_max of int
  | Decl_attr_card_min of int
  | Decl_attr_exn of exn (** open case *)

type (+'term, +'ty, 'inv) view =
  | Decl of id * decl * 'ty * decl_attr list
  | Axiom of ('term, 'ty, 'inv) axiom
  | TyDef of [`Data | `Codata] * 'ty mutual_types
  | Pred of [`Wf | `Not_wf] * [`Pred | `Copred] * ('term, 'ty, 'inv) pred_def list
  | Copy of ('term, 'ty) copy
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

type (+'term, +'ty, 'inv) t = {
  view: ('term, 'ty, 'inv) view;
  info: info;
}

type ('t, 'ty, 'inv) statement = ('t, 'ty, 'inv) t

let info_default = { loc=None; name=None; }

let mk_defined id ty = { defined_head=id; defined_ty=ty; }

let tydef_vars t = t.ty_vars
let tydef_id t = t.ty_id
let tydef_type t = t.ty_type
let tydef_cstors t = t.ty_cstors

let view t = t.view
let info t = t.info
let loc t = t.info.loc
let name t = t.info.name

let make_ ~info view = {info;view}

let mk_axiom ~info t = make_ ~info (Axiom t)
let mk_decl ~info ~attrs id k decl = make_ ~info (Decl (id,k,decl,attrs))
let mk_ty_def ~info k l = make_ ~info (TyDef (k, l))

let ty_decl ~info ~attrs id t = mk_decl ~info ~attrs id Decl_type t
let decl ~info ~attrs id t = mk_decl ~info ~attrs id Decl_fun t
let prop_decl ~info ~attrs id t = mk_decl ~info ~attrs id Decl_prop t
let axiom ~info l = mk_axiom ~info (Axiom_std l)
let axiom1 ~info t = axiom ~info [t]
let axiom_spec ~info t = mk_axiom ~info (Axiom_spec t)
let axiom_rec ~info t = mk_axiom ~info (Axiom_rec t)
let mk_pred ~info ~wf k l = make_ ~info (Pred (wf, k, l))
let pred ~info ~wf l = mk_pred ~info ~wf `Pred l
let copred ~info ~wf l = mk_pred ~info ~wf `Copred l
let data ~info l = mk_ty_def ~info `Data l
let codata ~info l = mk_ty_def ~info `Codata l
let copy ~info c = make_ ~info (Copy c)
let goal ~info t = make_ ~info (Goal t)

let mk_mutual_ty id ~ty_vars ~cstors ~ty =
  let ty_cstors =
    List.fold_left
      (fun m (cstor_name, cstor_args, cstor_type) ->
        ID.Map.add cstor_name {cstor_name; cstor_args; cstor_type} m)
      ID.Map.empty
      cstors
  in
  {ty_id=id; ty_type=ty; ty_vars; ty_cstors; }

let mk_copy ?pred ~of_ ~ty ~abstract ~concretize ~vars id =
  let copy_abstract, copy_abstract_ty = abstract in
  let copy_concretize, copy_concretize_ty = concretize in
  { copy_id=id;
    copy_vars=vars;
    copy_ty=ty;
    copy_of=of_;
    copy_abstract;
    copy_abstract_ty;
    copy_concretize;
    copy_concretize_ty;
    copy_pred=pred;
  }

(* find a definition for [id] in [cases], or None *)
let find_rec_def ~defs id =
  CCList.find_pred
    (fun def -> ID.equal def.rec_defined.defined_head id)
    defs

(* find a (co)inductive type declaration for [id] *)
let find_tydef ~defs id =
  CCList.find_pred
    (fun tydef -> ID.equal id tydef.ty_id)
    defs

(* find a definition for [id] in [cases], or None *)
let find_pred ~defs id =
  CCList.find_pred
    (fun def -> ID.equal def.pred_defined.defined_head id)
    defs

let map_defined ~f d = {
  defined_head=d.defined_head;
  defined_ty=f d.defined_ty;
}

let map_eqns_bind
: type acc a a1 b b1 inv_e inv_ty.
    bind:(acc -> b Var.t -> acc * b1 Var.t) ->
    term:(acc -> a -> a1) ->
    acc ->
    (a,b,<eqn:inv_e;ty:inv_ty;..>) equations ->
    (a1,b1,<eqn:inv_e;ty:inv_ty;..>) equations
= fun ~bind ~term acc eqn ->
    match eqn with
    | Eqn_nested l ->
        Eqn_nested
          (List.map
            (fun (vars,args,rhs,side) ->
              let acc, vars = Utils.fold_map bind acc vars in
              vars,
              List.map (term acc) args,
              term acc rhs,
              List.map (term acc) side)
            l)
    | Eqn_app (app_l, vars, lhs, rhs) ->
        let acc, vars = Utils.fold_map bind acc vars in
        Eqn_app (app_l, vars, term acc lhs, term acc rhs)
    | Eqn_single (vars,rhs) ->
        let acc, vars = Utils.fold_map bind acc vars in
        Eqn_single (vars, term acc rhs)

let map_eqns ~term ~ty c =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_eqns_bind () c ~bind ~term:(fun () -> term)

let map_copy_bind ~bind ~term ~ty acc c =
  let acc', copy_vars = Utils.fold_map bind acc c.copy_vars in
  { c with
    copy_vars;
    copy_of = ty acc' c.copy_of;
    copy_ty = ty acc c.copy_ty;
    copy_abstract_ty = ty acc' c.copy_abstract_ty;
    copy_concretize_ty = ty acc' c.copy_concretize_ty;
    copy_pred = CCOpt.map (term acc') c.copy_pred;
  }

let map_copy ~term ~ty c =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_copy_bind () c ~bind ~term:(fun () -> term) ~ty:(fun () -> ty)

external cast_eqns
: ('t, 'ty, <eqn:'inv;..>) equations ->
  ('t, 'ty, <eqn:'inv;..>) equations
= "%identity"

let map_rec_def_bind ~bind ~term ~ty acc t =
  let acc', vars = Utils.fold_map bind acc t.rec_vars in
  {
    rec_kind=t.rec_kind;
    rec_defined=map_defined ~f:(ty acc) t.rec_defined;
    rec_vars=vars;
    rec_eqns=map_eqns_bind ~bind ~term acc' t.rec_eqns;
  }

let map_rec_def ~term ~ty t =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_rec_def_bind ~bind ~term:(fun () -> term) ~ty:(fun () -> ty) () t

external cast_rec_def
: ('t, 'ty, <eqn:'inv;..>) rec_def ->
  ('t, 'ty, <eqn:'inv;..>) rec_def
= "%identity"

let map_rec_defs ~term ~ty t = List.map (map_rec_def ~term ~ty) t

let map_rec_defs_bind ~bind ~term ~ty acc t =
  List.map (map_rec_def_bind ~bind ~term ~ty acc) t

external cast_rec_defs
: ('t, 'ty, <eqn:'inv;..>) rec_defs ->
  ('t, 'ty, <eqn:'inv;..>) rec_defs
= "%identity"

let map_spec_defs ~term ~ty t = {
  spec_vars=List.map (Var.update_ty ~f:ty) t.spec_vars;
  spec_defined=List.map (map_defined ~f:ty) t.spec_defined;
  spec_axioms=List.map term t.spec_axioms;
}

let map_clause_bind
: type acc a a1 b b1 inv.
    bind:(acc -> b Var.t -> acc * b1 Var.t) ->
    term:(acc -> a -> a1) ->
    acc ->
    (a,b,<ind_preds:inv;..>) pred_clause ->
    (a1,b1,<ind_preds:inv;..>) pred_clause
= fun ~bind ~term acc c ->
  let Pred_clause c = c in
  let acc, vars = Utils.fold_map bind acc c.clause_vars in
  Pred_clause {
    clause_vars=vars;
    clause_guard=CCOpt.map (term acc) c.clause_guard;
    clause_concl=term acc c.clause_concl;
  }

let map_clause ~term ~ty c =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_clause_bind () c ~bind ~term:(fun () t -> term t)

let map_pred_bind
= fun ~bind ~term ~ty acc def ->
  let acc, ty_vars = Utils.fold_map bind acc def.pred_tyvars in
  let def' = {
    pred_defined=map_defined ~f:(ty acc) def.pred_defined;
    pred_tyvars=ty_vars;
    pred_clauses=List.map (map_clause_bind ~bind ~term acc) def.pred_clauses;
  } in
  def'

let map_pred ~term ~ty def =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_pred_bind () def ~bind ~term:(fun () -> term) ~ty:(fun () -> ty)

let map_preds_bind ~bind ~term ~ty acc l = List.map (map_pred_bind acc ~bind ~term ~ty) l

let map_preds ~term ~ty l = List.map (map_pred ~term ~ty) l

let map_ty_def_bind ~bind ~ty:fty acc l =
  List.map
    (fun tydef ->
      let acc', ty_vars = Utils.fold_map bind acc tydef.ty_vars in
      {tydef with
        ty_type=fty acc tydef.ty_type;
        ty_vars;
        ty_cstors=
          ID.Map.map
            (fun c -> {c with
              cstor_args=List.map (fty acc') c.cstor_args;
              cstor_type=fty acc' c.cstor_type
            })
            tydef.ty_cstors;
      }) l

let map_ty_def ~ty l =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_ty_def_bind () l ~bind ~ty:(fun () -> ty)

external cast_pred
: ('t, 'ty, <ind_preds:'inv;..>) pred_def ->
  ('t, 'ty, <ind_preds:'inv;..>) pred_def
= "%identity"

external cast_preds
: ('t, 'ty, <ind_preds:'inv;..>) pred_def list ->
  ('t, 'ty, <ind_preds:'inv;..>) pred_def list
= "%identity"

let map_bind ~bind ~term:ft ~ty:fty acc st =
  let info = st.info in
  match st.view with
  | Decl (id,k,t,attrs) ->
      mk_decl ~info ~attrs id k (fty acc t)
  | Axiom a ->
      begin match a with
      | Axiom_std l -> axiom ~info (List.map (ft acc) l)
      | Axiom_spec t ->
          axiom_spec ~info (map_spec_defs ~term:(ft acc) ~ty:(fty acc) t)
      | Axiom_rec t ->
          axiom_rec ~info (map_rec_defs_bind ~bind ~term:ft ~ty:fty acc t)
      end
  | TyDef (k, l) ->
      let l = map_ty_def_bind acc ~bind ~ty:fty l in
      mk_ty_def ~info k l
  | Pred (wf, k, preds) ->
      let preds = map_preds_bind ~bind ~term:ft ~ty:fty acc preds in
      mk_pred ~info ~wf k preds
  | Copy c -> copy ~info (map_copy_bind ~bind ~term:ft ~ty:fty acc c)
  | Goal t -> goal ~info (ft acc t)

let map ~term ~ty st =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_bind () st ~bind ~term:(fun () -> term) ~ty:(fun () -> ty)

let fold_defined ~ty acc d = ty acc d.defined_ty

let fold_eqns_bind (type inv) ~bind ~term ~ty b_acc acc (e:(_,_,inv) equations) =
  let fold_vars b_acc acc l = List.fold_left (fun acc v -> ty b_acc acc (Var.ty v)) acc l in
  match e with
  | Eqn_nested l ->
      List.fold_left
        (fun acc (vars,args,rhs,side) ->
          let acc = fold_vars b_acc acc vars in
          let b_acc = List.fold_left bind b_acc vars in
          let acc = List.fold_left (term b_acc) acc args in
          let acc = term b_acc acc rhs in
          List.fold_left (term b_acc) acc side)
        acc l
  | Eqn_app (_,vars,lhs,rhs) ->
      let acc = fold_vars b_acc acc vars in
      let b_acc = List.fold_left bind b_acc vars in
      let acc = term b_acc acc lhs in
      term b_acc acc rhs
  | Eqn_single (vars,t) ->
      let acc = List.fold_left (fun acc v -> ty b_acc acc (Var.ty v)) acc vars in
      let b_acc = List.fold_left bind b_acc vars in
      term b_acc acc t

let fold_clause_bind (type inv) ~bind ~term ~ty b_acc acc (c:(_,_,inv) pred_clause) =
  let Pred_clause c = c in
  let acc =
    List.fold_left (fun acc v -> ty b_acc acc (Var.ty v)) acc c.clause_vars in
  let b_acc = List.fold_left bind b_acc c.clause_vars in
  let acc = term b_acc acc c.clause_concl in
  CCOpt.fold (term b_acc) acc c.clause_guard

let fold_pred_bind (type inv) ~bind ~term ~ty b_acc acc (def:(_,_,inv) pred_def) =
  let acc = ty b_acc acc def.pred_defined.defined_ty in
  let b_acc = List.fold_left bind b_acc def.pred_tyvars in
  List.fold_left (fold_clause_bind ~term ~ty ~bind b_acc) acc def.pred_clauses

let fold_preds_bind ~bind ~term ~ty b_acc acc l =
  List.fold_left (fold_pred_bind ~bind ~term ~ty b_acc) acc l

let fold_bind (type inv) ~bind ~term:fterm ~ty:fty b_acc acc (st:(_,_,inv) t) =
  match st.view with
  | Decl (_, _, t, _) -> fty b_acc acc t
  | Axiom a ->
      begin match a with
      | Axiom_std l -> List.fold_left (fterm b_acc) acc l
      | Axiom_spec t ->
          let acc = List.fold_left (fold_defined ~ty:(fty b_acc)) acc t.spec_defined in
          List.fold_left (fterm b_acc) acc t.spec_axioms
      | Axiom_rec t ->
          List.fold_left
            (fun acc def ->
              let acc = fold_defined ~ty:(fty b_acc) acc def.rec_defined in
              fold_eqns_bind ~bind ~term:fterm ~ty:fty b_acc acc def.rec_eqns)
            acc t
      end
  | Pred (_, _, preds) -> fold_preds_bind ~bind ~term:fterm ~ty:fty b_acc acc preds
  | TyDef (_, l) ->
      List.fold_left
        (fun acc tydef ->
          let acc = fty b_acc acc tydef.ty_type in
          ID.Map.fold (fun _ c acc -> fty b_acc acc c.cstor_type) tydef.ty_cstors acc)
        acc l
  | Copy c ->
      let acc = List.fold_left (fun acc v -> fty b_acc acc (Var.ty v)) acc c.copy_vars in
      let b_acc = List.fold_left bind b_acc c.copy_vars in
      let acc =
        List.fold_left (fty b_acc) acc
          [c.copy_of; c.copy_ty; c.copy_concretize_ty; c.copy_abstract_ty] in
      CCOpt.fold (fterm b_acc) acc c.copy_pred
  | Goal t -> fterm b_acc acc t

let fold ~term:fterm ~ty:fty acc st =
  fold_bind () acc st
    ~bind:(fun () _ -> ()) ~term:(fun () -> fterm) ~ty:(fun () -> fty)

let iter ~term ~ty st =
  fold () st ~term:(fun () t -> term t) ~ty:(fun () t -> ty t)

let id_of_defined d = d.defined_head
let defined_of_rec r = r.rec_defined
let defined_of_recs l = Sequence.of_list l |> Sequence.map defined_of_rec
let defined_of_spec spec = Sequence.of_list spec.spec_defined

let fpf = Format.fprintf
let pplist ?(start="") ?(stop="") ~sep pp = CCFormat.list ~start ~stop ~sep pp

(* print list with prefix before every item *)
let pplist_prefix ~first ~pre pp out l =
  List.iteri
    (fun i x ->
      if i=0 then fpf out "%s" first else fpf out "@,%s" pre;
      pp out x)
    l

module Print(Pt : TI.PRINT)(Pty : TI.PRINT) = struct
  let pp_defined out d =
    fpf out "@[%a : %a@]" ID.print d.defined_head Pty.print d.defined_ty
  and pp_typed_var out v =
    fpf out "@[<2>%a:%a@]" Var.print_full v Pty.print_in_app (Var.ty v)

  let pp_defined_list out =
    fpf out "@[<v>%a@]" (pplist_prefix ~first:"" ~pre:" and " pp_defined)

  let print_eqns (type inv) id out (e:(_,_,inv) equations) =
    let pp_sides out l =
      if l=[] then ()
      else fpf out "@[<hv2>%a => @]@," (pplist ~sep:" && " Pt.print_in_app) l
    in
    match e with
    | Eqn_app (_, vars, lhs, rhs) ->
        if vars=[]
        then fpf out "@[<hv2>%a =@ %a@]" Pt.print lhs Pt.print rhs
        else fpf out "@[<hv2>forall @[<h>%a@].@ @[%a =@ %a@]@]"
          (pplist ~sep:" " pp_typed_var) vars Pt.print lhs Pt.print rhs
    | Eqn_nested l ->
        pplist ~sep:";"
          (fun out  (vars,args,rhs,side) ->
            if vars=[]
            then fpf out "@[<hv>%a@[<2>%a@ %a@] =@ %a@]"
              pp_sides side ID.print id
              (pplist ~sep:" " Pt.print_in_app) args Pt.print rhs
            else fpf out "@[<hv2>forall @[<h>%a@].@ %a@[<2>%a@ %a@] =@ %a@]"
              (pplist ~sep:" " pp_typed_var) vars pp_sides side ID.print id
              (pplist ~sep:" " Pt.print_in_app) args Pt.print rhs
          ) out l
    | Eqn_single (vars,rhs) ->
        fpf out "@[<2>%a %a =@ %a@]" ID.print id
          (pplist ~sep:" " pp_typed_var) vars Pt.print rhs

  let print_rec_def out d =
    fpf out "@[<hv2>%a :=@ %a@]"
      pp_defined d.rec_defined
      (print_eqns d.rec_defined.defined_head) d.rec_eqns

  let print_rec_defs out l =
    fpf out "@[<v>rec %a.@]"
      (pplist_prefix ~first:"" ~pre:"and " print_rec_def) l

  let print_spec_defs out d =
    let printerms = pplist ~sep:";" Pt.print in
    fpf out "@[<hv2>spec %a :=@ %a@]"
      pp_defined_list d.spec_defined printerms d.spec_axioms

  let print_pred_def out pred =
    let pp_clause (type inv) out (c:(_,_,inv) pred_clause) =
      let Pred_clause c = c in
      match c.clause_vars, c.clause_guard with
      | [], None -> Pt.print out c.clause_concl
      | [], Some g ->
          fpf out "@[<2>@[%a@]@ => @[%a@]@]" Pt.print g Pt.print c.clause_concl
      | _::_ as vars, None ->
          fpf out "@[<2>forall %a.@ @[%a@]@]"
          (pplist ~sep:" " Var.print_full) vars Pt.print c.clause_concl
      | _::_ as vars, Some g ->
          fpf out "@[<2>forall %a.@ @[%a@] =>@ @[%a@]@]"
          (pplist ~sep:" " Var.print_full) vars Pt.print g Pt.print c.clause_concl
    in
    fpf out "@[<hv2>@[%a@ : %a@] :=@ %a@]"
      ID.print pred.pred_defined.defined_head
      Pty.print pred.pred_defined.defined_ty
      (pplist ~sep:"; " pp_clause) pred.pred_clauses

  let print_pred_defs out preds = pplist ~sep:" and " print_pred_def out preds

  let print_copy out c =
    let pp_pred out = function
      | None -> ()
      | Some p -> fpf out "@,@[<2>pred@ @[%a@]@]" Pt.print p
    in
    fpf out
      "@[<v2>copy @[%a %a :=@ @[%a@]@]@ abstract %a : %a@ concretize %a : %a%a@]"
      ID.print c.copy_id
      (CCFormat.list ~start:"" ~stop:"" ~sep:" " Var.print_full) c.copy_vars
      Pty.print c.copy_of
      ID.print c.copy_abstract Pty.print c.copy_abstract_ty
      ID.print c.copy_concretize Pty.print c.copy_concretize_ty
      pp_pred c.copy_pred

  let pp_attr out = function
    | Decl_attr_card_max i -> fpf out "max_card %d" i
    | Decl_attr_card_min i -> fpf out "min_card %d" i
    | Decl_attr_exn e -> CCFormat.string out (Printexc.to_string e)

  let pp_attrs out = function
    | [] -> ()
    | l -> fpf out "@ [@[%a@]]" (pplist ~sep:"," pp_attr) l

  let print_tydef out tydef =
    let ppcstors out c =
      fpf out "@[<hv2>%a %a@]"
        ID.print c.cstor_name (pplist ~sep:" " Pty.print_in_app) c.cstor_args in
    fpf out "@[<hv2>@[%a %a@] :=@ @[<hv>%a@]@]"
      ID.print tydef.ty_id
      (pplist ~sep:" " Var.print_full) tydef.ty_vars
      (pplist_prefix ~first:" | " ~pre:" | " ppcstors)
        (ID.Map.to_list tydef.ty_cstors |> List.map snd)

  let print_tydefs out (k,l) =
    fpf out "@[<hv2>%s@ "
      (match k with `Data -> "data" | `Codata -> "codata");
    List.iteri
      (fun i tydef ->
        if i>0 then fpf out "@,and ";
        print_tydef out tydef)
      l;
    fpf out ".@]"

  let print out t = match t.view with
  | Decl (id,_,t,attrs) ->
      fpf out "@[<2>val %a@ : %a%a.@]" ID.print id Pty.print t pp_attrs attrs
  | Axiom a ->
      begin match a with
      | Axiom_std l ->
          fpf out "@[<hv2>axiom@ %a.@]" (pplist ~sep:"; " Pt.print) l
      | Axiom_spec t -> print_spec_defs out t
      | Axiom_rec t -> print_rec_defs out t
      end
  | Pred (wf, k, l) ->
      let pp_wf out = function `Wf -> fpf out "[wf]" | `Not_wf -> () in
      let pp_k out = function `Pred -> fpf out "pred" | `Copred -> fpf out "copred" in
      fpf out "@[<hv>%a%a %a.@]" pp_k k pp_wf wf print_pred_defs l
  | TyDef (k, l) -> print_tydefs out (k,l)
  | Copy c -> fpf out "@[<2>%a.@]" print_copy c
  | Goal t -> fpf out "@[<2>goal %a.@]" Pt.print t
end
