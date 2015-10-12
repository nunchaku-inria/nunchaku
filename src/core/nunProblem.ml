
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
    | Goal of 'term

  type ('a, 'b) t = {
    view: ('a, 'b) view;
    loc: Loc.t option;
  }

  let case_defined t = t.case_defined
  let case_axioms t = t.case_axioms
  let case_alias t = t.case_alias
  let case_vars t = t.case_vars

  let view t = t.view
  let loc t = t.loc

  let make_ ?loc view = {loc;view}

  let mk_axiom ?loc t = make_ ?loc (Axiom t)
  let mk_decl ?loc id k decl = make_ ?loc (Decl (id,k,decl))

  let ty_decl ?loc id t = mk_decl ?loc id Decl_type t
  let decl ?loc id t = mk_decl ?loc id Decl_fun t
  let prop_decl ?loc id t = mk_decl ?loc id Decl_prop t
  let axiom ?loc l = mk_axiom ?loc (Axiom_std l)
  let axiom1 ?loc t = axiom ?loc [t]
  let axiom_spec ?loc t = mk_axiom ?loc (Axiom_spec t)
  let axiom_rec ?loc t = mk_axiom ?loc (Axiom_rec t)
  let goal ?loc t = make_ ?loc (Goal t)

  let map_case ~term ~ty t = {
    case_vars=List.map (Var.update_ty ~f:ty) t.case_vars;
    case_defined=term t.case_defined;
    case_axioms=List.map term t.case_axioms;
    case_alias=Var.update_ty ~f:ty t.case_alias;
  }

  let map_cases ~term ~ty t = List.map (map_case ~term ~ty) t

  let map ~term:ft ~ty:fty st =
    let loc = st.loc in
    match st.view with
    | Decl (id,k,t) ->
        mk_decl ?loc id k (fty t)
    | Axiom a ->
        begin match a with
        | Axiom_std l -> axiom ?loc (List.map ft l)
        | Axiom_spec t ->
            axiom_spec ?loc (map_cases ~term:ft ~ty:fty t)
        | Axiom_rec t ->
            axiom_rec ?loc (map_cases ~term:ft ~ty:fty t)
        end
    | Goal t -> goal ?loc (ft t)

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
    | Goal t -> term acc t

  let print pt pty out t = match t.view with
    | Decl (id,_,t) ->
        fpf out "@[<2>val %a@ : %a.@]" ID.print_no_id id pty t
    | Axiom a ->
        let print_cases out t =
          let print_case out c =
            fpf out "@[<v2>@[%a@] as %a :=@ %a@]@,"
              pt c.case_defined Var.print c.case_alias
              (CCFormat.list ~start:"" ~stop:"" ~sep:"; " pt) c.case_axioms
          in
          fpf out "@[<hov>%a@]"
            (CCFormat.list ~start:"" ~stop:"" ~sep:" and " print_case) t
        in
        begin match a with
        | Axiom_std l ->
            fpf out "@[<2>axiom %a.@]"
              (CCFormat.list ~start:"" ~stop:"" ~sep:";" pt) l
        | Axiom_spec t -> fpf out "@[<2>spec %a.@]" print_cases t
        | Axiom_rec t -> fpf out "@[<2>rec %a.@]" print_cases t
        end
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

let map ~term ~ty p = {
  statements=CCList.map (Statement.map ~term ~ty) p.statements;
}

let print pt pty out problem =
  fpf out "@[<v2>{%a@]@,}"
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
  let check_new_ ~sigma id =
    if ID.Map.mem id sigma
      then ill_formed_ (CCFormat.sprintf "symbol %a declared twice" ID.print id)
  in
  List.fold_left
    (fun sigma st -> match Statement.view st with
      | Statement.Decl (id,_,ty) ->
          check_new_ ~sigma id;
          ID.Map.add id ty sigma
      | Statement.Goal _
      | Statement.Axiom _ -> sigma
    ) init pb.statements

module Model = struct
  type 't t = ('t * 't) list

  let map ~f m = CCList.map (fun (x,y) -> f x, f y) m

  let print pt out m =
    let pp_pair out (t,u) = fpf out "@[<hv2>%a ->@ %a@]" pt t pt u in
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
