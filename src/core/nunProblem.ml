
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = NunLocation
module ID = NunID

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit
type 'a or_error = [`Ok of 'a | `Error of string]

let fpf = Format.fprintf

module Statement = struct
  type ('term, 'ty) view =
    | TyDecl of id * 'ty (** uninterpreted type *)
    | Decl of id * 'ty (** uninterpreted symbol *)
    | Def of id * 'ty * 'term (** defined function symbol *)
    | PropDef of id * 'ty * 'term (** defined symbol of type Prop. The type is prop. *)
    | Axiom of 'term
    | Goal of 'term

  type ('a, 'b) t = {
    view: ('a, 'b) view;
    loc: Loc.t option;
  }

  let view t = t.view
  let loc t = t.loc

  let make_ ?loc view = {loc;view}

  let ty_decl ?loc v t = make_ ?loc (TyDecl (v,t))
  let decl ?loc v t = make_ ?loc (Decl (v,t))
  let prop_def ?loc v ~prop t = make_ ?loc (PropDef (v,prop,t))
  let def ?loc v ~ty t = make_ ?loc (Def (v,ty,t))
  let axiom ?loc t = make_ ?loc (Axiom t)
  let goal ?loc t = make_ ?loc (Goal t)

  let map ~term:ft ~ty:fty st =
    let loc = st.loc in
    match st.view with
    | TyDecl (id,ty) -> ty_decl ?loc id (fty ty)
    | Decl (id,ty) -> decl ?loc id (fty ty)
    | PropDef (id,prop,t) -> prop_def ?loc id ~prop:(fty prop) (ft t)
    | Def (id,ty,t) -> def ?loc id ~ty:(fty ty) (ft t)
    | Axiom t -> axiom ?loc (ft t)
    | Goal t -> goal ?loc (ft t)

  let print pt pty out t =
    match t.view with
    | TyDecl (v, ty) -> fpf out "@[<2>val %a@ : %a.@]" ID.print_no_id v pty ty
    | Decl (v, ty) -> fpf out "@[<2>val %a@ : %a.@]" ID.print_no_id v pty ty
    | PropDef (v, prop, t) ->
        fpf out "@[<2>def %a@ : %a@ := %a.@]"
          ID.print_no_id v pty prop pt t
    | Def (v, ty, t) ->
        fpf out "@[<2>def %a@ : %a@ := %a.@]"
          ID.print_no_id v pty ty pt t
    | Axiom t -> fpf out "@[<2>axiom %a.@]" pt t
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
  fpf out "@[<v2>{%a}@]"
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
      | Statement.TyDecl (id,ty)
      | Statement.Decl (id,ty)
      | Statement.Def (id,ty,_) ->
          check_new_ ~sigma id;
          ID.Map.add id ty sigma
      | Statement.PropDef (id,prop,_) ->
          check_new_ ~sigma id;
          ID.Map.add id prop sigma
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
