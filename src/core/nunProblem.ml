
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = NunLocation
module ID = NunID
module Var = NunVar

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

let fpf = Format.fprintf

module Statement = struct
  type decl =
    | Decl_type
    | Decl_fun
    | Decl_prop


  (** defines [t], aliased as local variable [v], with the [axioms].
    All the type variables [alpha_1, ..., alpha_n] are free in [t]
    and in [axioms], and no other type variable should occur. *)
  type ('t,'ty) case = {
    case_vars: 'ty NunVar.t list; (* alpha_1, ..., alpha_n *)
    case_defined: 't; (* t *)
    case_alias: 'ty NunVar.t; (* v *)
    case_axioms: 't list; (* axioms *)
  }

  (* mutual definition of several terms *)
  type ('t,'ty) mutual_cases = ('t,'ty) case list

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
    | Axiom_spec of ('t,'ty) mutual_cases
      (** Axioms can be safely ignored, they are consistent *)
    | Axiom_rec of ('t,'ty) mutual_cases
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

  let case_defined t = t.case_defined
  let case_axioms t = t.case_axioms
  let case_alias t = t.case_alias
  let case_vars t = t.case_vars

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

  let map_case ~term ~ty t = {
    case_vars=List.map (Var.update_ty ~f:ty) t.case_vars;
    case_defined=term t.case_defined;
    case_axioms=List.map term t.case_axioms;
    case_alias=Var.update_ty ~f:ty t.case_alias;
  }

  let map_cases ~term ~ty t = List.map (map_case ~term ~ty) t

  let map ~term:ft ~ty:fty st =
    let info = st.info in
    match st.view with
    | Decl (id,k,t) ->
        mk_decl ~info id k (fty t)
    | Axiom a ->
        begin match a with
        | Axiom_std l -> axiom ~info (List.map ft l)
        | Axiom_spec t ->
            axiom_spec ~info (map_cases ~term:ft ~ty:fty t)
        | Axiom_rec t ->
            axiom_rec ~info (map_cases ~term:ft ~ty:fty t)
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

  let fold ~term ~ty acc st = match st.view with
    | Decl (_, _, t) -> ty acc t
    | Axiom a ->
        begin match a with
        | Axiom_std l -> List.fold_left term acc l
        | Axiom_spec t
        | Axiom_rec t ->
            List.fold_left
              (fun acc case ->
                let acc = term acc case.case_defined in
                let acc = ty acc (Var.ty case.case_alias) in
                let acc = List.fold_left
                  (fun acc v -> ty acc (Var.ty v))
                  acc case.case_vars in
                List.fold_left term acc case.case_axioms
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

  let print pt pty out t = match t.view with
    | Decl (id,_,t) ->
        fpf out "@[<2>val %a@ : %a.@]" ID.print_name id pty t
    | Axiom a ->
        let print_cases ~what out l =
          let print_case out c =
            fpf out "@[<v2>@[%a@] as %a :=@ @[<v>%a@]@]"
              pt c.case_defined Var.print c.case_alias
              (pplist ~sep:"; " pt) c.case_axioms
          in
          fpf out "@[<hov>%s " what;
          List.iteri
            (fun i case ->
              if i>0 then fpf out "@,and ";
              print_case out case
            ) l;
          fpf out ".@]"
        in
        begin match a with
        | Axiom_std l ->
            fpf out "@[<hv2>axiom@ %a.@]" (pplist ~sep:"; " pt) l
        | Axiom_spec t -> print_cases ~what:"spec" out t
        | Axiom_rec t -> print_cases ~what:"rec" out t
        end
    | TyDef (k, l) ->
        let pty_in_app out t = fpf out "(%a)" pty t in
        let ppcstors out c =
          fpf out "@[<hv2>%a %a@]"
            ID.print_name c.cstor_name (pplist ~sep:" " pty_in_app) c.cstor_args in
        let print_def out tydef =
          fpf out "@[<v2>%a %a :=@ @[<v>%a@]@]"
            ID.print_name tydef.ty_id
            (pplist ~sep:" " Var.print) tydef.ty_vars
            (pplist ~sep:" | " ppcstors) tydef.ty_cstors
        in
        fpf out "@[<hv2>%s@ %a.@]"
          (match k with `Data -> "data" | `Codata -> "codata")
          (pplist ~sep:" and " print_def) l
    | Goal t -> fpf out "@[<2>goal %a.@]" pt t

  let print_list pt pty out l =
    fpf out "@[<v>%a@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" (print pt pty)) l
end

module Signature = struct
  type 'ty t = 'ty NunID.Map.t

  let empty = ID.Map.empty

  let mem ~sigma id = ID.Map.mem id sigma
  let find_exn ~sigma id = ID.Map.find id sigma
  let find ~sigma id =
    try Some (find_exn ~sigma id)
    with Not_found -> None

  let declare ~sigma id ty = ID.Map.add id ty sigma
end

type ('t, 'ty) t = {
  statements : ('t, 'ty) Statement.t list;
}

let statements t = t.statements

let make statements =
  { statements; }

let map_statements ~f st = {
  statements=CCList.map f st.statements;
}

let map_with ?(before=fun _ -> []) ?(after=fun _ -> []) ~term ~ty p = {
  statements=CCList.flat_map
    (fun st ->
      let st' = Statement.map ~term ~ty st in
      before () @ [st'] @ after ()
    )
    p.statements;
}

let map ~term ~ty pb = map_with ~term ~ty pb

let print pt pty out problem =
  fpf out "{@,%a@,}"
    (Statement.print_list pt pty) problem.statements

exception IllFormed of string
(** Ill-formed problem *)

let () = Printexc.register_printer
  (function
    | IllFormed msg -> Some (Printf.sprintf "problem is ill-formed: %s" msg)
    | _ -> None
  )

let ill_formed_ msg = raise (IllFormed msg)

let goal pb =
  let rec aux acc l = match acc, l with
    | Some g, [] -> g
    | None, [] -> ill_formed_ "no goal"
    | None, {Statement.view=Statement.Goal g;_} :: l' ->
        aux (Some g) l'
    | Some _, {Statement.view=Statement.Goal _;_} :: _ ->
        ill_formed_ "several goals"
    | acc, _ :: l' -> aux acc l'
  in
  aux None pb.statements

let signature ?(init=ID.Map.empty) pb =
  let module St = Statement in
  let declare_ ~sigma id ty =
    if ID.Map.mem id sigma
      then ill_formed_ (CCFormat.sprintf "symbol %a declared twice" ID.print id);
    ID.Map.add id ty sigma
  in
  List.fold_left
    (fun sigma st -> match St.view st with
      | St.Decl (id,_,ty) -> declare_ ~sigma id ty
      | St.TyDef (_,l) ->
          List.fold_left
            (fun sigma tydef ->
              let sigma = declare_ ~sigma tydef.St.ty_id tydef.St.ty_type in
              List.fold_left
                (fun sigma c -> declare_ ~sigma c.St.cstor_name c.St.cstor_type)
                sigma tydef.St.ty_cstors
            ) sigma l
      | St.Goal _
      | St.Axiom _ -> sigma
    ) init pb.statements

module Model = struct
  type 't t = ('t * 't) list

  let map ~f m = CCList.map (fun (x,y) -> f x, f y) m

  let print pt out m =
    let pp_pair out (t,u) = fpf out "@[<hv2>@[%a@]@ ->@ @[%a@]@]" pt t pt u in
    Format.fprintf out "@[<v>%a@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_pair) m
end

module Res = struct
  type 't model = 't Model.t

  type 't t =
    | Unsat
    | Sat of 't model  (** model maps terms to values *)
    | Timeout

  let map ~f t = match t with
    | Unsat -> Unsat
    | Timeout -> Timeout
    | Sat model -> Sat (Model.map ~f model)

  let fpf = Format.fprintf

  let print pt out = function
    | Unsat -> fpf out "unsat"
    | Timeout -> fpf out "timeout"
    | Sat m ->
        fpf out "@[<2>sat {@,%a}@]" (Model.print pt) m
end
