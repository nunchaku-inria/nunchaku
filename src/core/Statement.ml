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

type ('t, 'ty, 'kind) equations =
  | Eqn_linear :
      ('ty var list (* universally quantified vars, also arguments to [f] *)
      * 't (* right-hand side of equation *)
      * 't list (* side conditions *)
      ) list
      -> ('t, 'ty, <eqn:[`Linear];..>) equations
  | Eqn_nested :
      ('ty var list (* universally quantified vars *)
      * 't list (* arguments (patterns) to the defined term *)
      * 't  (* right-hand side of equation *)
      * 't list (* additional conditions *)
      ) list
      -> ('t, 'ty, <eqn:[`Nested];..>) equations
  | Eqn_single :
      'ty var list (* function arguments *)
      *  't (* RHS *)
      -> ('t, 'ty, <eqn:[`Single];..>) equations

type ('t,'ty,'kind) rec_def = {
  rec_defined: 'ty defined;
  rec_kind: decl;
  rec_vars: 'ty var list; (* type variables in definitions *)
  rec_eqns: ('t, 'ty,'kind) equations; (* list of equations defining the term *)
}

type ('t, 'ty,'kind) rec_defs = ('t, 'ty,'kind) rec_def list

type ('t, 'ty) spec_defs = {
  spec_vars: 'ty var list; (* type variables used by defined terms *)
  spec_defined: 'ty defined list;  (* terms being specified together *)
  spec_axioms: 't list;  (* free-form axioms *)
}

(** A type constructor: name + type of arguments *)
type 'ty ty_constructor = {
  cstor_name: id; (** Name *)
  cstor_args: 'ty list; (** type arguments *)
  cstor_type: 'ty; (** type of the constructor (shortcut) *)
}

(** A (co)inductive type. The type variables [ty_vars] occur freely in
    the constructors' types. *)
type 'ty tydef = {
  ty_id : id;
  ty_vars : 'ty Var.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor ID.Map.t;
}

(** Mutual definitions of several types *)
type 'ty mutual_types = 'ty tydef list

(** Flavour of axiom *)
type ('t,'ty,'kind) axiom =
  | Axiom_std of 't list
    (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
    (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty,'kind) rec_defs
    (** Axioms are part of an admissible (partial) definition *)

type ('t, 'ty) pred_clause_cell = {
  clause_vars: 'ty var list; (* universally quantified vars *)
  clause_guard: 't option;
  clause_concl: 't;
}

type (_, _, _) pred_clause =
  | Pred_clause :
    ('t, 'ty) pred_clause_cell ->
    ('t, 'ty, <ind_preds:[`Present];..>) pred_clause

type ('t, 'ty, 'inv) pred_def = {
  pred_defined: 'ty defined;
  pred_tyvars: 'ty var list;
  pred_clauses: ('t, 'ty, 'inv) pred_clause list;
}

type ('term, 'ty, 'inv) view =
  | Decl of id * decl * 'ty
  | Axiom of ('term, 'ty, 'inv) axiom
  | TyDef of [`Data | `Codata] * 'ty mutual_types
  | Pred of [`Wf | `Not_wf] * [`Pred | `Copred] * ('term, 'ty, 'inv) pred_def list
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

type ('term, 'ty, 'inv) t = {
  view: ('term, 'ty, 'inv) view;
  info: info;
}

type ('t, 'ty, 'inv) statement = ('t, 'ty, 'inv) t

let info_default = { loc=None; name=None; }

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
let mk_decl ~info id k decl = make_ ~info (Decl (id,k,decl))
let mk_ty_def ~info k l = make_ ~info (TyDef (k, l))

let ty_decl ~info id t = mk_decl ~info id Decl_type t
let decl ~info id t = mk_decl ~info id Decl_fun t
let prop_decl ~info id t = mk_decl ~info id Decl_prop t
let axiom ~info l = mk_axiom ~info (Axiom_std l)
let axiom1 ~info t = axiom ~info [t]
let axiom_spec ~info t = mk_axiom ~info (Axiom_spec t)
let axiom_rec ~info t = mk_axiom ~info (Axiom_rec t)
let mk_pred ~info ~wf k l = make_ ~info (Pred (wf, k, l))
let pred ~info ~wf l = mk_pred ~info ~wf `Pred l
let copred ~info ~wf l = mk_pred ~info ~wf `Copred l
let data ~info l = mk_ty_def ~info `Data l
let codata ~info l = mk_ty_def ~info `Codata l
let goal ~info t = make_ ~info (Goal t)

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

let map_eqns
: type a a1 b b1 inv.
    term:(a -> a1) -> ty:(b -> b1) ->
    (a,b,<eqn:inv;..>) equations -> (a1,b1,<eqn:inv;..>) equations
= fun ~term ~ty eqn ->
    match eqn with
    | Eqn_nested l ->
        Eqn_nested
          (List.map
            (fun (vars,args,rhs,side) ->
              List.map (Var.update_ty ~f:ty) vars,
              List.map term args,
              term rhs,
              List.map term side)
            l)
    | Eqn_linear l ->
        Eqn_linear
          (List.map
            (fun (vars,rhs,side) ->
              List.map (Var.update_ty ~f:ty) vars,
              term rhs,
              List.map term side)
            l)
    | Eqn_single (vars,rhs) ->
        Eqn_single (List.map (Var.update_ty ~f:ty) vars, term rhs)

let cast_eqns
: type inv.
  ('t, 'ty, <eqn:inv;..>) equations ->
  ('t, 'ty, <eqn:inv;..>) equations
= function
  | Eqn_nested l -> Eqn_nested l
  | Eqn_linear l -> Eqn_linear l
  | Eqn_single (vars,rhs) -> Eqn_single (vars,rhs)

let map_clause ~term ~ty c =
  { clause_vars=List.map (Var.update_ty ~f:ty) c.clause_vars;
    clause_concl=term c.clause_concl;
    clause_guard=CCOpt.map term c.clause_guard;
  }

let map_rec_def ~term ~ty t = {
  rec_kind=t.rec_kind;
  rec_defined=map_defined ~f:ty t.rec_defined;
  rec_vars=List.map (Var.update_ty ~f:ty) t.rec_vars;
  rec_eqns=map_eqns ~term ~ty t.rec_eqns;
}

let cast_rec_def
: type inv.
  ('t, 'ty, <eqn:inv;..>) rec_def ->
  ('t, 'ty, <eqn:inv;..>) rec_def
= fun def -> Obj.magic def

let map_rec_defs ~term ~ty t = List.map (map_rec_def ~term ~ty) t

let cast_rec_defs
: type inv.
  ('t, 'ty, <eqn:inv;..>) rec_defs ->
  ('t, 'ty, <eqn:inv;..>) rec_defs
= fun t -> (Obj.magic t)

let map_spec_defs ~term ~ty t = {
  spec_vars=List.map (Var.update_ty ~f:ty) t.spec_vars;
  spec_defined=List.map (map_defined ~f:ty) t.spec_defined;
  spec_axioms=List.map term t.spec_axioms;
}

let map_clause
: type a a1 b b1 inv.
    term:(a -> a1) -> ty:(b -> b1) ->
    (a,b,<ind_preds:inv;..>) pred_clause ->
    (a1,b1,<ind_preds:inv;..>) pred_clause
= fun ~term ~ty c ->
  let Pred_clause c = c in
  Pred_clause {
    clause_vars=List.map (Var.update_ty ~f:ty) c.clause_vars;
    clause_guard=CCOpt.map term c.clause_guard;
    clause_concl=term c.clause_concl;
  }

let map_pred
= fun ~term ~ty def ->
  let def' = {
    pred_defined=map_defined ~f:ty def.pred_defined;
    pred_tyvars=List.map (Var.update_ty ~f:ty) def.pred_tyvars;
    pred_clauses=List.map (map_clause ~term ~ty) def.pred_clauses;
  } in
  def'

let map_preds ~term ~ty l = List.map (map_pred ~term ~ty) l

let map ~term:ft ~ty:fty st =
  let info = st.info in
  match st.view with
  | Decl (id,k,t) ->
      mk_decl ~info id k (fty t)
  | Axiom a ->
      begin match a with
      | Axiom_std l -> axiom ~info (List.map ft l)
      | Axiom_spec t ->
          axiom_spec ~info (map_spec_defs ~term:ft ~ty:fty t)
      | Axiom_rec t ->
          axiom_rec ~info (map_rec_defs ~term:ft ~ty:fty t)
      end
  | TyDef (k, l) ->
      let l = List.map
        (fun tydef ->
          {tydef with
            ty_type=fty tydef.ty_type;
            ty_vars=List.map (Var.update_ty ~f:fty) tydef.ty_vars;
            ty_cstors=
              ID.Map.map
                (fun c -> {c with
                  cstor_args=List.map fty c.cstor_args;
                  cstor_type=fty c.cstor_type
                })
                tydef.ty_cstors;
          }) l
      in
      mk_ty_def ~info k l
  | Pred (wf, k, preds) ->
      let preds = map_preds ~term:ft ~ty:fty preds in
      mk_pred ~info ~wf k preds
  | Goal t -> goal ~info (ft t)

let fold_defined ~ty acc d = ty acc d.defined_ty

let fold_eqns_ (type inv) ~term ~ty acc (e:(_,_,inv) equations) =
  let fold_vars acc l = List.fold_left (fun acc v -> ty acc (Var.ty v)) acc l in
  match e with
  | Eqn_nested l ->
      List.fold_left
        (fun acc (vars,args,rhs,side) ->
          let acc = fold_vars acc vars in
          let acc = List.fold_left term acc args in
          let acc = term acc rhs in
          List.fold_left term acc side)
        acc l
  | Eqn_linear l ->
      List.fold_left
        (fun acc (vars,rhs,side) ->
          let acc = fold_vars acc vars in
          let acc = term acc rhs in
          List.fold_left term acc side)
        acc l
  | Eqn_single (vars,t) ->
      let acc = List.fold_left (fun acc v -> ty acc (Var.ty v)) acc vars in
      term acc t

let fold_clause (type inv) ~term ~ty acc (c:(_,_,inv) pred_clause) =
  let Pred_clause c = c in
  let acc =
    List.fold_left (fun acc v -> ty acc (Var.ty v)) acc c.clause_vars in
  let acc = term acc c.clause_concl in
  CCOpt.fold term acc c.clause_guard

let fold_pred (type inv) ~term ~ty acc (def:(_,_,inv) pred_def) =
  let acc = ty acc def.pred_defined.defined_ty in
  List.fold_left (fold_clause ~term ~ty) acc def.pred_clauses

let fold_preds ~term ~ty acc l =
  List.fold_left (fold_pred ~term ~ty) acc l

let fold (type inv) ~term ~ty acc (st:(_,_,inv) t) =
  match st.view with
  | Decl (_, _, t) -> ty acc t
  | Axiom a ->
      begin match a with
      | Axiom_std l -> List.fold_left term acc l
      | Axiom_spec t ->
          let acc = List.fold_left (fold_defined ~ty) acc t.spec_defined in
          List.fold_left term acc t.spec_axioms
      | Axiom_rec t ->
          List.fold_left
            (fun acc def ->
              let acc = fold_defined ~ty acc def.rec_defined in
              fold_eqns_ ~term ~ty acc def.rec_eqns
            )
            acc t
      end
  | Pred (_, _, preds) -> fold_preds ~term ~ty acc preds
  | TyDef (_, l) ->
      List.fold_left
        (fun acc tydef ->
          let acc = ty acc tydef.ty_type in
          ID.Map.fold (fun _ c acc -> ty acc c.cstor_type) tydef.ty_cstors acc
        ) acc l
  | Goal t -> term acc t

let fpf = Format.fprintf
let pplist ?(start="") ?(stop="") ~sep pp = CCFormat.list ~start ~stop ~sep pp

(* print list with prefix before every item *)
let pplist_prefix ~first ~pre pp out l =
  List.iteri
    (fun i x ->
      if i=0 then fpf out "%s" first else fpf out "@,%s" pre;
      pp out x)
    l

let print (type a)(type b)
(module Pt : TI.PRINT with type t = a)
(module Pty : TI.PRINT with type t = b) out t =
  match t.view with
  | Decl (id,_,t) ->
      fpf out "@[<2>val %a@ : %a.@]" ID.print id Pty.print t
  | Axiom a ->
      let pp_defined out d =
        fpf out "@[%a : %a@]" ID.print d.defined_head Pty.print d.defined_ty
      and pp_typed_var out v =
        fpf out "@[<2>%a:%a@]" Var.print v Pty.print (Var.ty v)
      in
      let pp_rec_defs out l =
        let pp_sides out l =
          if l=[] then ()
          else fpf out "@[<hv2>%a => @]@," (pplist ~sep:" && " Pt.print_in_app) l
        in
        (* print equations *)
        let pp_eqns (type inv) id out (e:(_,_,inv) equations) =
          match e with
          | Eqn_linear l  ->
              pplist ~sep:";"
                (fun out (vars,rhs,side) ->
                  if vars=[]
                  then fpf out "@[<hv>%a%a =@ %a@]" pp_sides side ID.print id Pt.print rhs
                  else fpf out "@[<hv2>forall @[<h>%a@].@ %a@[<2>%a@ %a@] =@ %a@]"
                    (pplist ~sep:" " pp_typed_var) vars pp_sides side ID.print id
                    (pplist ~sep:" " pp_typed_var) vars Pt.print rhs
                ) out l
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
        in
        let pp_def out d =
          fpf out "@[<hv2>%a :=@ %a@]"
            pp_defined d.rec_defined
            (pp_eqns d.rec_defined.defined_head) d.rec_eqns
        in
        fpf out "@[<v>rec %a.@]"
          (pplist_prefix ~first:"" ~pre:"and " pp_def) l
      and pp_spec_defs out d =
        let printerms = pplist ~sep:";" Pt.print in
        let pp_defined_list out =
          fpf out "@[<v>%a@]" (pplist_prefix ~first:"" ~pre:" and " pp_defined)
        in
        fpf out "@[<hv2>spec %a :=@ %a@]"
          pp_defined_list d.spec_defined printerms d.spec_axioms
      in
      begin match a with
      | Axiom_std l ->
          fpf out "@[<hv2>axiom@ %a.@]" (pplist ~sep:"; " Pt.print) l
      | Axiom_spec t -> pp_spec_defs out t
      | Axiom_rec t -> pp_rec_defs out t
      end
  | Pred (wf, k, l) ->
      let pp_wf out = function `Wf -> fpf out "[wf]" | `Not_wf -> () in
      let pp_k out = function `Pred -> fpf out "pred" | `Copred -> fpf out "copred" in
      let pp_clause (type inv) out (c:(_,_,inv) pred_clause) =
        let Pred_clause c = c in
        match c.clause_vars, c.clause_guard with
        | [], None -> Pt.print out c.clause_concl
        | [], Some g ->
            fpf out "@[<2>@[%a@]@ => @[%a@]@]" Pt.print g Pt.print c.clause_concl
        | _::_ as vars, None ->
            fpf out "@[<2>forall %a.@ @[%a@]@]"
            (pplist ~sep:" " Var.print) vars Pt.print c.clause_concl
        | _::_ as vars, Some g ->
            fpf out "@[<2>forall %a.@ @[%a@] =>@ @[%a@]@]"
            (pplist ~sep:" " Var.print) vars Pt.print g Pt.print c.clause_concl
      in
      let pp_pred out pred =
        fpf out "@[<hv2>@[%a@ : %a@] :=@ %a@]"
          ID.print pred.pred_defined.defined_head
          Pty.print pred.pred_defined.defined_ty
          (pplist ~sep:"; " pp_clause) pred.pred_clauses
      in
      let pp_preds out preds = pplist ~sep:" and " pp_pred out preds in
      fpf out "@[<hv>%a%a %a.@]" pp_k k pp_wf wf pp_preds l
  | TyDef (k, l) ->
      let ppcstors out c =
        fpf out "@[<hv2>%a %a@]"
          ID.print c.cstor_name (pplist ~sep:" " Pty.print_in_app) c.cstor_args in
      let print_def out tydef =
        fpf out "@[<hv2>@[%a %a@] :=@ @[<hv>%a@]@]"
          ID.print tydef.ty_id
          (pplist ~sep:" " Var.print) tydef.ty_vars
          (pplist_prefix ~first:" | " ~pre:" | " ppcstors)
            (ID.Map.to_list tydef.ty_cstors |> List.map snd)
      in
      fpf out "@[<hv2>%s@ "
        (match k with `Data -> "data" | `Codata -> "codata");
      List.iteri
        (fun i tydef ->
          if i>0 then fpf out "@,and ";
          print_def out tydef
        ) l;
      fpf out ".@]"
  | Goal t -> fpf out "@[<2>goal %a.@]" Pt.print t

module Print(Pt : TI.PRINT)(Pty : TI.PRINT) = struct
  let print out st = print (module Pt)(module Pty) out st
end
