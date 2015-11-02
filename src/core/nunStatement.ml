(* This file is free software, part of nunchaku. See file "license" for more details. *)

module Var = NunVar
module ID = NunID

type id = ID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t
type 'a printer = Format.formatter -> 'a -> unit

type decl =
  | Decl_type
  | Decl_fun
  | Decl_prop

type ('t,'ty) defined = {
  defined_term: 't;  (* term being defined/specified *)
  defined_head: id; (* head symbol of [defined_term] *)
  defined_ty_args: 'ty list; (* type arguments. *)
}

type ('t, 'ty) equation =
  'ty var list (* universally quantified vars *)
  * 't list (* arguments to the defined term *)
  * 't  (* right-hand side of equation *)

type ('t,'ty) rec_def = {
  rec_vars: 'ty var list; (* alpha_1, ..., alpha_n *)
  rec_defined: ('t, 'ty) defined;
  rec_eqns: ('t, 'ty) equation list; (* list of equations defining the term *)
}

type ('t, 'ty) rec_defs = ('t, 'ty) rec_def list

type ('t, 'ty) spec_defs = {
  spec_vars: 'ty var list; (* type variables used by defined terms *)
  spec_defined: ('t, 'ty) defined list;  (* terms being specified together *)
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
  ty_vars : 'ty NunVar.t list;
  ty_type : 'ty; (** shortcut for [type -> type -> ... -> type] *)
  ty_cstors : 'ty ty_constructor list;
}

(** Mutual definitions of several types *)
type 'ty mutual_types = 'ty tydef list

(** Flavour of axiom *)
type ('t,'ty) axiom =
  | Axiom_std of 't list
    (** Axiom list that can influence consistency (no assumptions) *)
  | Axiom_spec of ('t,'ty) spec_defs
    (** Axioms can be safely ignored, they are consistent *)
  | Axiom_rec of ('t,'ty) rec_defs
    (** Axioms are part of an admissible (partial) definition *)

type ('term, 'ty) view =
  | Decl of id * decl * 'ty
  | Axiom of ('term, 'ty) axiom
  | TyDef of [`Data | `Codata] * 'ty mutual_types
  | Goal of 'term

(** Additional informations on the statement *)
type info = {
  loc: loc option;
  name: string option;
}

let info_default = { loc=None; name=None; }

type ('term, 'ty) t = {
  view: ('term, 'ty) view;
  info: info;
}

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
let data ~info l = mk_ty_def ~info `Data l
let codata ~info l = mk_ty_def ~info `Codata l
let goal ~info t = make_ ~info (Goal t)

let map_defined ~term ~ty d = {
  defined_head=d.defined_head;
  defined_ty_args=List.map ty d.defined_ty_args;
  defined_term=term d.defined_term;
}

let map_eqn ~term ~ty (vars,args,rhs) =
  List.map (Var.update_ty ~f:ty) vars, List.map term args, term rhs

let map_rec_def ~term ~ty t = {
  rec_vars=List.map (Var.update_ty ~f:ty) t.rec_vars;
  rec_defined=map_defined ~term ~ty t.rec_defined;
  rec_eqns=List.map (map_eqn ~term ~ty) t.rec_eqns;
}

let map_rec_defs ~term ~ty t = List.map (map_rec_def ~term ~ty) t

let map_spec_defs ~term ~ty t = {
  spec_vars=List.map (Var.update_ty ~f:ty) t.spec_vars;
  spec_defined=List.map (map_defined ~term ~ty) t.spec_defined;
  spec_axioms=List.map term t.spec_axioms;
}

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
              List.map
                (fun c -> {c with
                  cstor_args=List.map fty c.cstor_args;
                  cstor_type=fty c.cstor_type
                })
                tydef.ty_cstors;
          }) l
      in
      mk_ty_def ~info k l
  | Goal t -> goal ~info (ft t)

let fold_defined ~term ~ty acc d =
  let acc = List.fold_left ty acc d.defined_ty_args in
  term acc d.defined_term

let fold ~term ~ty acc st =
  let fold_vars acc l = List.fold_left (fun acc v -> ty acc (Var.ty v)) acc l in
  match st.view with
  | Decl (_, _, t) -> ty acc t
  | Axiom a ->
      begin match a with
      | Axiom_std l -> List.fold_left term acc l
      | Axiom_spec t ->
          let acc = fold_vars acc t.spec_vars in
          let acc = List.fold_left (fold_defined ~term ~ty) acc t.spec_defined in
          List.fold_left term acc t.spec_axioms
      | Axiom_rec t ->
          List.fold_left
            (fun acc def ->
              let acc = fold_defined ~term ~ty acc def.rec_defined in
              let acc = fold_vars acc def.rec_vars in
              List.fold_left
                (fun acc (vars,args,rhs) ->
                  let acc = fold_vars acc vars in
                  let acc = List.fold_left term acc args in
                  term acc rhs
                ) acc def.rec_eqns
            )
            acc t
      end
  | TyDef (_, l) ->
      List.fold_left
        (fun acc tydef ->
          let acc = ty acc tydef.ty_type in
          List.fold_left (fun acc c -> ty acc c.cstor_type) acc tydef.ty_cstors
        ) acc l
  | Goal t -> term acc t

let pplist ?(start="") ?(stop="") ~sep pp = CCFormat.list ~start ~stop ~sep pp

let fpf = Format.fprintf

let print ?pty_in_app pt pty out t =
  let pty_in_app = CCOpt.get (fun out -> fpf out "(%a)" pty) pty_in_app in
  match t.view with
  | Decl (id,_,t) ->
      fpf out "@[<2>val %a@ : %a.@]" ID.print_name id pty t
  | Axiom a ->
      let pp_defined out d = fpf out "@[<h>%a@]" pt d.defined_term
      and pp_typed_var out v =
        fpf out "@[<2>%a:%a@]" Var.print v pty (Var.ty v)
      in
      let pp_rec_defs out l =
        (* print equation *)
        let pp_eqn t out (vars,args,rhs) =
          if vars=[]
          then fpf out "@[<hv>%a %a =@ %a@]"
            pt t (pplist ~sep:" " pt) args pt rhs
          else fpf out "@[<hv2>forall @[<h>%a@].@ @[<hv>%a %a =@ %a@]@]"
            (pplist ~sep:" " pp_typed_var) vars pt t
            (pplist ~sep:" " pt) args pt rhs
        in
        let pp_eqns t = pplist ~sep:";" (pp_eqn t) in
        let pp_def out d =
          fpf out "@[<hv2>%a :=@ %a@]"
            pp_defined d.rec_defined
            (pp_eqns d.rec_defined.defined_term) d.rec_eqns
        in
        fpf out "@[<hov>rec ";
        List.iteri
          (fun i def ->
            if i>0 then fpf out "@,and ";
            pp_def out def
          ) l;
        fpf out ".@]"
      and pp_spec_defs out d =
        let ppterms = pplist ~sep:";" pt in
        let pp_defined_list out =
          fpf out "@[<v>%a@]" (pplist ~sep:" and " pp_defined)
        in
        fpf out "@[<hv2>spec @[<hv>%a@] :=@ %a@]"
          pp_defined_list d.spec_defined ppterms d.spec_axioms
      in
      begin match a with
      | Axiom_std l ->
          fpf out "@[<hv2>axiom@ %a.@]" (pplist ~sep:"; " pt) l
      | Axiom_spec t -> pp_spec_defs out t
      | Axiom_rec t -> pp_rec_defs out t
      end
  | TyDef (k, l) ->
      let ppcstors out c =
        fpf out "@[<hv2>%a %a@]"
          ID.print_name c.cstor_name (pplist ~sep:" " pty_in_app) c.cstor_args in
      let print_def out tydef =
        fpf out "@[<hv2>%a %a :=@ @[<v>%a@]@]"
          ID.print_name tydef.ty_id
          (pplist ~sep:" " Var.print) tydef.ty_vars
          (pplist ~sep:" | " ppcstors) tydef.ty_cstors
      in
      fpf out "@[<hv2>%s@ "
        (match k with `Data -> "data" | `Codata -> "codata");
      List.iteri
        (fun i tydef ->
          if i>0 then fpf out "@,and ";
          print_def out tydef
        ) l;
      fpf out ".@]"
  | Goal t -> fpf out "@[<2>goal %a.@]" pt t

let print_list ?pty_in_app pt pty out l =
  fpf out "@[<v>%a@]"
    (CCFormat.list ~start:"" ~stop:"" ~sep:"" (print ?pty_in_app pt pty)) l
