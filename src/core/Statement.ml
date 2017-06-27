(* This file is free software, part of nunchaku. See file "license" for more details. *)

type id = ID.t
type 'a var = 'a Var.t
type loc = Location.t
type 'a printer = Format.formatter -> 'a -> unit

(** Attribute on declarations *)
type decl_attr =
  | Attr_card_max of int (** maximal cardinality of type constraint *)
  | Attr_card_min of int (** minimal cardinality of type constraint *)
  | Attr_card_max_hint of int (** maximal cardinality of type as redundant hint *)
  | Attr_card_min_hint of int (** minimal cardinality of type as redundant hint *)
  | Attr_incomplete (** encoding of some type with some values removed *)
  | Attr_abstract (** encoding of some type where some values are conflated *)
  | Attr_infinite (** infinite uninterpreted type *)
  | Attr_can_be_empty (** empty type allowed? *)
  | Attr_finite_approx of ID.t (** finite approximation of an infinite type *)
  | Attr_infinite_upcast (** cast finite approx to infinite type *)
  | Attr_pseudo_prop (** encoding of [prop] *)
  | Attr_pseudo_true (** encoding of [true_ : pseudo_prop] *)
  | Attr_is_handle_cstor
  (** [Attr_is_handle_cstor] means that the ID is the binary type symbol
        that represents arrows for partially applied functions *)
  | Attr_app_val
  (** [Attr_app_val] means that the ID being defined is an "application function"
      that is used to encode HO partial application into regular FO total
      application. There is only one application symbol per type. *)
  | Attr_proto_val of ID.t * int
  (** [Attr_proto_val (f,k)] means the ID currently being declared is
      the [k]-th "proto" function used for default values. This "proto" is
      paired to the symbol [f], which is an application symbol of type
      [handle -> a_1 -> ... -> a_n -> ret], where the proto
      has type [handle -> a_k]. *)
  | Attr_never_box (** This function should never be boxed in ElimRec *)

type 'ty defined = {
  defined_head: id; (* symbol being defined *)
  defined_ty: 'ty; (* type of the head symbol *)
  defined_attrs: decl_attr list;
}

type (+'t, +'ty) equations =
  | Eqn_nested of
      ('ty var list (* universally quantified vars *)
       * 't list (* arguments (patterns) to the defined term *)
       * 't  (* right-hand side of equation *)
       * 't list (* additional conditions *)
      ) list
  | Eqn_single of
      'ty var list (* function arguments *)
      *  't (* RHS *)
  | Eqn_app of
      ID.t list (* application symbols *)
      * 'ty var list (* quantified vars *)
      * 't (* LHS of equation *)
      * 't (* RHS of equation *)

type (+'t,+'ty) rec_def = {
  rec_defined: 'ty defined;
  rec_ty_vars: 'ty var list; (* type variables in definitions *)
  rec_eqns: ('t, 'ty) equations; (* list of equations defining the term *)
}

type (+'t, +'ty) rec_defs = ('t, 'ty) rec_def list

type (+'t, +'ty) spec_defs = {
  spec_ty_vars: 'ty var list; (* type variables used by defined terms *)
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
type +'ty data_type = {
  ty_id : id;
  ty_vars : 'ty Var.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor ID.Map.t;
}

(** Mutual definitions of several types *)
type +'ty data_types = 'ty data_type list


(** Flavour of axiom *)
type (+'t,+'ty) axiom =
  | Axiom_std of 't list
  (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
  (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty) rec_defs
  (** Axioms are part of an admissible (partial) definition *)

type (+'t, +'ty) pred_clause = {
  clause_vars: 'ty var list; (* universally quantified vars *)
  clause_guard: 't option;
  clause_concl: 't;
}

type (+'t, +'ty) pred_def = {
  pred_defined: 'ty defined;
  pred_tyvars: 'ty var list;
  pred_clauses: ('t, 'ty) pred_clause list;
}

type 't copy_wrt =
  | Wrt_nothing
  | Wrt_subset of 't (* invariant (copy_of -> prop) *)
  | Wrt_quotient of [`Partial | `Total] * 't (* invariant (copy_of -> copy_of -> prop) *)

type (+'t, +'ty) copy = {
  copy_id: ID.t; (* new name *)
  copy_vars: 'ty Var.t list; (* list of type variables *)
  copy_ty: 'ty;  (* type of [copy_id], of the form [type -> type -> ... -> type] *)
  copy_of: 'ty; (* [id vars] is a copy of [of_]. Set of variables = vars *)
  copy_to: 'ty; (* [id vars] *)
  copy_wrt: 't copy_wrt;
  copy_abstract: ID.t; (* [of -> id vars] *)
  copy_abstract_ty: 'ty;
  copy_concrete: ID.t; (* [id vars -> of] *)
  copy_concrete_ty: 'ty;
}

type (+'term, +'ty) view =
  | Decl of 'ty defined
  | Axiom of ('term, 'ty) axiom
  | TyDef of [`Data | `Codata] * 'ty data_types
  | Pred of [`Wf | `Not_wf] * [`Pred | `Copred] * ('term, 'ty) pred_def list
  | Copy of ('term, 'ty) copy
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

type (+'term, +'ty) t = {
  view: ('term, 'ty) view;
  info: info;
}

type (+'t, +'ty) statement = ('t, 'ty) t

let info_default = { loc=None; name=None; }
let info_of_loc loc = { loc; name=None; }

let mk_defined ~attrs id ty =
  { defined_head=id; defined_ty=ty; defined_attrs=attrs; }

let data_vars t = t.ty_vars
let data_id t = t.ty_id
let data_type t = t.ty_type
let data_cstors t = t.ty_cstors

let view t = t.view
let info t = t.info
let loc t = t.info.loc
let name t = t.info.name

let make_ ~info view = {info;view}

let mk_axiom ~info t = make_ ~info (Axiom t)
let mk_ty_def ~info k l = make_ ~info (TyDef (k, l))

let decl_of_defined ~info d= make_ ~info (Decl d)
let decl ~info ~attrs id t = make_ ~info (Decl (mk_defined ~attrs id t))
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

let mk_data_type id ~ty_vars ~cstors ~ty =
  let ty_cstors =
    List.fold_left
      (fun m (cstor_name, cstor_args, cstor_type) ->
         ID.Map.add cstor_name {cstor_name; cstor_args; cstor_type} m)
      ID.Map.empty
      cstors
  in
  {ty_id=id; ty_type=ty; ty_vars; ty_cstors; }

let mk_copy ~wrt ~of_ ~to_ ~ty ~abstract ~concrete ~vars id =
  let copy_abstract, copy_abstract_ty = abstract in
  let copy_concrete, copy_concrete_ty = concrete in
  { copy_id=id;
    copy_vars=vars;
    copy_ty=ty;
    copy_of=of_;
    copy_to=to_;
    copy_wrt=wrt;
    copy_abstract;
    copy_abstract_ty;
    copy_concrete;
    copy_concrete_ty;
  }

(* find a definition for [id] in [cases], or None *)
let find_rec_def ~defs id =
  CCList.find_pred
    (fun def -> ID.equal def.rec_defined.defined_head id)
    defs

(* find a (co)inductive type declaration for [id] *)
let find_data_type ~defs id =
  CCList.find_pred
    (fun tydef -> ID.equal id tydef.ty_id)
    defs

(* find a definition for [id] in [cases], or None *)
let find_pred ~defs id =
  CCList.find_pred
    (fun def -> ID.equal def.pred_defined.defined_head id)
    defs

let map_defined ~f d = {
  d with
    defined_head=d.defined_head;
    defined_ty=f d.defined_ty;
}

let map_eqns_bind ~bind ~term acc pol eqn =
  match eqn with
    | Eqn_nested l ->
      Eqn_nested
        (List.map
           (fun (vars,args,rhs,side) ->
              let acc, vars = Utils.fold_map bind acc vars in
              vars,
              List.map (term acc pol) args,
              term acc pol rhs,
              List.map (term acc pol) side)
           l)
    | Eqn_app (app_l, vars, lhs, rhs) ->
      let acc, vars = Utils.fold_map bind acc vars in
      Eqn_app (app_l, vars, term acc pol lhs, term acc pol rhs)
    | Eqn_single (vars,rhs) ->
      let acc, vars = Utils.fold_map bind acc vars in
      Eqn_single (vars, term acc pol rhs)

let map_eqns ~term ~ty c =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_eqns_bind () Polarity.NoPol c ~bind ~term:(fun () _pol -> term)

let map_copy_wrt f wrt = match wrt with
  | Wrt_nothing -> Wrt_nothing
  | Wrt_subset p -> Wrt_subset (f p)
  | Wrt_quotient (tty, r) -> Wrt_quotient (tty, f r)

let map_copy_bind ~bind ~term ~ty acc c =
  let acc', copy_vars = Utils.fold_map bind acc c.copy_vars in
  { c with
      copy_vars;
      copy_of = ty acc' c.copy_of;
      copy_to = ty acc' c.copy_to;
      copy_ty = ty acc c.copy_ty;
      copy_wrt = map_copy_wrt (term acc' Polarity.NoPol) c.copy_wrt;
      copy_abstract_ty = ty acc' c.copy_abstract_ty;
      copy_concrete_ty = ty acc' c.copy_concrete_ty;
  }

let map_copy ~term ~ty c =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_copy_bind () c ~bind ~term:(fun () _pol -> term) ~ty:(fun () -> ty)

let map_rec_def_bind ~bind ~term ~ty acc t =
  let acc', vars = Utils.fold_map bind acc t.rec_ty_vars in
  let pol = ID.polarity t.rec_defined.defined_head in
  {
    rec_defined=map_defined ~f:(ty acc) t.rec_defined;
    rec_ty_vars=vars;
    rec_eqns=map_eqns_bind ~bind ~term acc' pol t.rec_eqns;
  }

let map_rec_def ~term ~ty t =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_rec_def_bind ~bind ~term:(fun () _pol -> term) ~ty:(fun () -> ty) () t

let map_rec_defs ~term ~ty t = List.map (map_rec_def ~term ~ty) t

let map_rec_defs_bind ~bind ~term ~ty acc t =
  List.map (map_rec_def_bind ~bind ~term ~ty acc) t

let map_spec_defs_bind ~bind ~term ~ty acc t =
  let acc', vars = Utils.fold_map bind acc t.spec_ty_vars in
  { spec_ty_vars=vars;
    spec_defined=List.map (map_defined ~f:(ty acc)) t.spec_defined;
    spec_axioms=List.map (term acc' Polarity.Pos) t.spec_axioms;
  }

let map_spec_defs ~term ~ty t =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_spec_defs_bind () t ~bind ~term:(fun _ _pol -> term) ~ty:(fun _ -> ty)

let map_clause_bind ~bind ~term acc c =
  let acc, vars = Utils.fold_map bind acc c.clause_vars in
  {
    clause_vars=vars;
    clause_guard=CCOpt.map (term acc Polarity.Neg) c.clause_guard;
    clause_concl=term acc Polarity.Pos c.clause_concl;
  }

let map_clause ~term ~ty c =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_clause_bind () c ~bind ~term:(fun () _pol t -> term t)

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
  map_pred_bind () def ~bind ~term:(fun () _pol -> term) ~ty:(fun () -> ty)

let map_preds_bind ~bind ~term ~ty acc l =
  List.map (map_pred_bind acc ~bind ~term ~ty) l

let map_preds ~term ~ty l = List.map (map_pred ~term ~ty) l

let map_data_bind ~bind ~ty:fty acc tydef =
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
  }

let map_data_type ~ty l =
  let bind () v = (), Var.update_ty v ~f:ty in
  map_data_bind () l ~bind ~ty:(fun () -> ty)

let map_data_types ~ty l = List.map (map_data_type ~ty) l

let map_bind ~bind ~term:ft ~ty:fty acc st =
  let info = st.info in
  match st.view with
    | Decl d ->
      let d = map_defined d ~f:(fty acc) in
      decl_of_defined ~info d
    | Axiom a ->
      begin match a with
        | Axiom_std l -> axiom ~info (List.map (ft acc Polarity.Pos) l)
        | Axiom_spec t ->
          axiom_spec ~info (map_spec_defs_bind ~bind ~term:ft ~ty:fty acc t)
        | Axiom_rec t ->
          axiom_rec ~info (map_rec_defs_bind ~bind ~term:ft ~ty:fty acc t)
      end
    | TyDef (k, l) ->
      let l = List.map (map_data_bind acc ~bind ~ty:fty) l in
      mk_ty_def ~info k l
    | Pred (wf, k, preds) ->
      let preds = map_preds_bind ~bind ~term:ft ~ty:fty acc preds in
      mk_pred ~info ~wf k preds
    | Copy c -> copy ~info (map_copy_bind ~bind ~term:ft ~ty:fty acc c)
    | Goal t -> goal ~info (ft acc Polarity.Pos t)

let map ~term ~ty st =
  let bind () v = (), Var.update_ty ~f:ty v in
  map_bind () st ~bind ~term:(fun () _pol -> term) ~ty:(fun () -> ty)

let fold_defined ~ty acc d = ty acc d.defined_ty

let fold_eqns_bind ~bind ~term:fterm ~ty:fty b_acc pol acc (e:(_,_) equations) =
  let fold_vars b_acc acc l =
    List.fold_left (fun acc v -> fty b_acc acc (Var.ty v)) acc l
  in
  match e with
    | Eqn_nested l ->
      List.fold_left
        (fun acc (vars,args,rhs,side) ->
           let acc = fold_vars b_acc acc vars in
           let b_acc = List.fold_left bind b_acc vars in
           let acc = List.fold_left (fterm b_acc pol) acc args in
           let acc = fterm b_acc pol acc rhs in
           List.fold_left (fterm b_acc pol) acc side)
        acc l
    | Eqn_app (_,vars,lhs,rhs) ->
      let acc = fold_vars b_acc acc vars in
      let b_acc = List.fold_left bind b_acc vars in
      let acc = fterm b_acc pol acc lhs in
      fterm b_acc pol acc rhs
    | Eqn_single (vars,t) ->
      let acc = List.fold_left (fun acc v -> fty b_acc acc (Var.ty v)) acc vars in
      let b_acc = List.fold_left bind b_acc vars in
      fterm b_acc pol acc t

let fold_clause_bind ~bind ~term ~ty k b_acc acc (c:(_,_) pred_clause) =
  let acc =
    List.fold_left (fun acc v -> ty b_acc acc (Var.ty v)) acc c.clause_vars in
  let pol = match k with `Pred -> Polarity.Pos | `Copred -> Polarity.Neg in
  let b_acc = List.fold_left bind b_acc c.clause_vars in
  let acc = term b_acc pol acc c.clause_concl in
  CCOpt.fold (term b_acc (Polarity.inv pol)) acc c.clause_guard

let fold_pred_bind ~bind ~term ~ty k b_acc acc (def:(_,_) pred_def) =
  let acc = ty b_acc acc def.pred_defined.defined_ty in
  let b_acc = List.fold_left bind b_acc def.pred_tyvars in
  List.fold_left (fold_clause_bind ~term ~ty ~bind k b_acc) acc def.pred_clauses

let fold_preds_bind ~bind ~term ~ty k b_acc acc l =
  List.fold_left (fold_pred_bind ~bind ~term ~ty k b_acc) acc l

let fold_bind ~bind ~term:fterm ~ty:fty b_acc acc (st:(_,_) t) =
  match st.view with
    | Decl {defined_ty=t; _} -> fty b_acc acc t
    | Axiom a ->
      begin match a with
        | Axiom_std l -> List.fold_left (fterm b_acc Polarity.Pos) acc l
        | Axiom_spec t ->
          let acc = List.fold_left (fold_defined ~ty:(fty b_acc)) acc t.spec_defined in
          List.fold_left (fterm b_acc Polarity.Pos) acc t.spec_axioms
        | Axiom_rec t ->
          List.fold_left
            (fun acc def ->
               let acc = fold_defined ~ty:(fty b_acc) acc def.rec_defined in
               let pol = ID.polarity def.rec_defined.defined_head in
               fold_eqns_bind ~bind ~term:fterm ~ty:fty b_acc pol acc def.rec_eqns)
            acc t
      end
    | Pred (_, k, preds) ->
      fold_preds_bind ~bind ~term:fterm ~ty:fty k b_acc acc preds
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
          [c.copy_of; c.copy_ty; c.copy_to] in
      begin match c.copy_wrt with
        | Wrt_nothing -> acc
        | Wrt_subset p -> fterm b_acc Polarity.NoPol acc p
        | Wrt_quotient (_, r) -> fterm b_acc Polarity.NoPol acc r
      end
    | Goal t -> fterm b_acc Polarity.Pos acc t

let fold ~term:fterm ~ty:fty acc st =
  fold_bind () acc st
    ~bind:(fun () _ -> ()) ~term:(fun () _pol -> fterm) ~ty:(fun () -> fty)

let iter ~term ~ty st =
  fold () st ~term:(fun () t -> term t) ~ty:(fun () t -> ty t)

let id_of_defined d = d.defined_head
let ty_of_defined d = d.defined_ty
let attrs_of_defined d = d.defined_attrs
let defined_of_rec r = r.rec_defined
let defined_of_recs l = Sequence.of_list l |> Sequence.map defined_of_rec
let defined_of_spec spec = Sequence.of_list spec.spec_defined
let defined_of_pred p = p.pred_defined
let defined_of_preds l = Sequence.of_list l |> Sequence.map defined_of_pred
let defined_of_cstor c : _ defined = mk_defined ~attrs:[] c.cstor_name c.cstor_type
let defined_of_data d yield =
  yield (mk_defined ~attrs:[] d.ty_id d.ty_type);
  ID.Map.iter (fun _ c -> yield (defined_of_cstor c)) d.ty_cstors
let defined_of_datas l =
  Sequence.of_list l |> Sequence.flat_map defined_of_data
let defined_of_copy c yield : unit =
  yield (mk_defined ~attrs:[] c.copy_id c.copy_ty);
  yield (mk_defined ~attrs:[] c.copy_abstract c.copy_abstract_ty);
  yield (mk_defined ~attrs:[] c.copy_concrete c.copy_concrete_ty);
  ()

let defined_seq (stmt:(_,_)t): _ defined Sequence.t =
  begin match view stmt with
    | Decl d -> Sequence.return d
    | Axiom (Axiom_rec defs) -> defined_of_recs defs
    | Axiom (Axiom_spec s) -> defined_of_spec s
    | Axiom (Axiom_std _)
    | Goal _ -> Sequence.empty
    | TyDef (_,l) -> defined_of_datas l
    | Pred (_,_,l) -> defined_of_preds l
    | Copy c -> defined_of_copy c
  end

let ids_of_copy c =
  Sequence.of_list [c.copy_id; c.copy_concrete; c.copy_abstract]

let fpf = Format.fprintf
let pplist ~sep pp = Utils.pp_list ~sep pp

(* print list with prefix before every item *)
let pplist_prefix ~first ~pre pp out l =
  List.iteri
    (fun i x ->
       if i=0 then fpf out "%s" first else fpf out "@,%s" pre;
       pp out x)
    l

let pp_attr out = function
  | Attr_card_max i -> fpf out "max_card %d" i
  | Attr_card_min i -> fpf out "min_card %d" i
  | Attr_card_max_hint i -> fpf out "max_card_hint %d" i
  | Attr_card_min_hint i -> fpf out "min_card_hint %d" i
  | Attr_can_be_empty -> CCFormat.string out "can_be_empty"
  | Attr_incomplete -> CCFormat.string out "incomplete"
  | Attr_abstract -> CCFormat.string out "abstract"
  | Attr_infinite -> CCFormat.string out "infinite"
  | Attr_finite_approx id -> fpf out "approx_of %a" ID.pp id
  | Attr_infinite_upcast -> CCFormat.string out "upcast"
  | Attr_pseudo_prop -> CCFormat.string out "pseudo_prop"
  | Attr_pseudo_true -> CCFormat.string out "pseudo_true"
  | Attr_app_val -> CCFormat.string out "app_symbol"
  | Attr_is_handle_cstor -> CCFormat.string out "handle_type"
  | Attr_proto_val (id, n) -> fpf out "proto_%d_of_%a" n ID.pp id
  | Attr_never_box -> CCFormat.string out "never_box"

let pp_attrs out = function
  | [] -> ()
  | l -> fpf out "@ [@[%a@]]" (pplist ~sep:"," pp_attr) l

module type PRINT_TERM = sig
  type t
  val pp : t CCFormat.printer
  val pp' : Precedence.t -> t CCFormat.printer
end

module Print(Pt : PRINT_TERM)(Pty : PRINT_TERM) = struct
  let pp_defined out d =
    fpf out "@[%a : %a%a@]"
      ID.pp d.defined_head Pty.pp d.defined_ty pp_attrs d.defined_attrs
  and pp_typed_var out v =
    fpf out "@[<2>%a:%a@]" Var.pp_full v (Pty.pp' Precedence.App) (Var.ty v)

  let pp_defined_list out =
    fpf out "@[<v>%a@]" (pplist_prefix ~first:"" ~pre:" and " pp_defined)

  let pp_eqns id out (e:(_,_) equations) =
    let pp_sides out l =
      if l=[] then ()
      else fpf out "@[<hv2>%a => @]@,"
          (pplist ~sep:" && " (Pt.pp' Precedence.App)) l
    in
    match e with
      | Eqn_app (_, vars, lhs, rhs) ->
        if vars=[]
        then fpf out "@[<hv2>%a =@ %a@]" Pt.pp lhs Pt.pp rhs
        else fpf out "@[<hv2>forall @[<h>%a@].@ @[%a =@ %a@]@]"
            (pplist ~sep:" " pp_typed_var) vars Pt.pp lhs Pt.pp rhs
      | Eqn_nested l ->
        pplist ~sep:";"
          (fun out  (vars,args,rhs,side) ->
             if vars=[]
             then fpf out "@[<hv>%a@[<2>%a@ %a@] =@ %a@]"
                 pp_sides side ID.pp id
                 (pplist ~sep:" " (Pt.pp' Precedence.App)) args Pt.pp rhs
             else fpf out "@[<hv2>forall @[<h>%a@].@ %a@[<2>%a@ %a@] =@ %a@]"
                 (pplist ~sep:" " pp_typed_var) vars pp_sides side ID.pp id
                 (pplist ~sep:" " (Pt.pp' Precedence.App)) args Pt.pp rhs
          ) out l
      | Eqn_single (vars,rhs) ->
        fpf out "@[<2>%a %a =@ %a@]" ID.pp id
          (pplist ~sep:" " pp_typed_var) vars Pt.pp rhs

  let pp_rec_def out d =
    fpf out "@[<hv2>%a :=@ %a@]"
      pp_defined d.rec_defined
      (pp_eqns d.rec_defined.defined_head) d.rec_eqns

  let pp_rec_defs out l =
    fpf out "@[<v>rec %a.@]"
      (pplist_prefix ~first:"" ~pre:"and " pp_rec_def) l

  let pp_spec_defs out d =
    let printerms = pplist ~sep:";" Pt.pp in
    fpf out "@[<hv2>spec %a :=@ %a.@]"
      pp_defined_list d.spec_defined printerms d.spec_axioms

  let pp_clause out (c:(_,_) pred_clause) =
    match c.clause_vars, c.clause_guard with
      | [], None -> Pt.pp out c.clause_concl
      | [], Some g ->
        fpf out "@[<2>@[%a@]@ => @[%a@]@]" Pt.pp g Pt.pp c.clause_concl
      | _::_ as vars, None ->
        fpf out "@[<2>forall %a.@ @[%a@]@]"
          (pplist ~sep:" " Var.pp_full) vars Pt.pp c.clause_concl
      | _::_ as vars, Some g ->
        fpf out "@[<2>forall %a.@ @[%a@] =>@ @[%a@]@]"
          (pplist ~sep:" " Var.pp_full) vars Pt.pp g Pt.pp c.clause_concl

  let pp_clauses out l =
    fpf out "@[<v>%a@]" (pplist ~sep:"; " pp_clause) l

  let pp_pred_def out pred =
    fpf out "@[<hv2>@[%a@] :=@ %a@]"
      pp_defined pred.pred_defined
      pp_clauses pred.pred_clauses

  let pp_pred_defs out preds = pplist ~sep:" and " pp_pred_def out preds

  let pp_copy out c =
    let pp_wrt out = function
      | Wrt_nothing -> ()
      | Wrt_subset p -> fpf out "@,@[<2>subset@ @[%a@]@]" Pt.pp p
      | Wrt_quotient (`Total, r) -> fpf out "@,@[<2>quotient@ @[%a@]@]" Pt.pp r
      | Wrt_quotient (`Partial, r) -> fpf out "@,@[<2>partial_quotient@ @[%a@]@]" Pt.pp r
    in
    fpf out
      "@[<v2>copy @[<4>%a %a :=@ @[%a@]@]@ %a\
       @[abstract %a : @[%a@]@]@ \
       @[concrete %a : @[%a@]@]@]"
      ID.pp c.copy_id
      (Utils.pp_list ~sep:" " Var.pp_full) c.copy_vars
      Pty.pp c.copy_of
      pp_wrt c.copy_wrt
      ID.pp c.copy_abstract Pty.pp c.copy_abstract_ty
      ID.pp c.copy_concrete Pty.pp c.copy_concrete_ty

  let pp_data_type out tydef =
    let ppcstors out c =
      fpf out "@[<hv2>%a %a@]"
        ID.pp c.cstor_name (pplist ~sep:" " (Pty.pp' Precedence.App)) c.cstor_args in
    fpf out "@[<hv2>@[%a %a@] :=@ @[<hv>%a@]@]"
      ID.pp tydef.ty_id
      (pplist ~sep:" " Var.pp_full) tydef.ty_vars
      (pplist_prefix ~first:" | " ~pre:" | " ppcstors)
      (ID.Map.to_list tydef.ty_cstors |> List.map snd)

  let pp_data_types out (k,l) =
    fpf out "@[<hv2>%s@ "
      (match k with `Data -> "data" | `Codata -> "codata");
    List.iteri
      (fun i tydef ->
         if i>0 then fpf out "@,and ";
         pp_data_type out tydef)
      l;
    fpf out ".@]"

  let pp out t = match t.view with
    | Decl d ->
      fpf out "@[<2>val %a.@]" pp_defined d
    | Axiom a ->
      begin match a with
        | Axiom_std l ->
          fpf out "@[<hv2>axiom@ %a.@]" (pplist ~sep:"; " Pt.pp) l
        | Axiom_spec t -> pp_spec_defs out t
        | Axiom_rec t -> pp_rec_defs out t
      end
    | Pred (wf, k, l) ->
      let pp_wf out = function `Wf -> fpf out "[wf]" | `Not_wf -> () in
      let pp_k out = function `Pred -> fpf out "pred" | `Copred -> fpf out "copred" in
      fpf out "@[<hv>%a%a %a.@]" pp_k k pp_wf wf pp_pred_defs l
    | TyDef (k, l) -> pp_data_types out (k,l)
    | Copy c -> fpf out "@[<2>%a.@]" pp_copy c
    | Goal t -> fpf out "@[<2>goal %a.@]" Pt.pp t
end
