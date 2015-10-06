
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = NunLocation
module ID = NunID

type loc = Loc.t
type id = ID.t
type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

module Statement = struct
  type ('term, 'ty) view =
    | Decl of id * 'ty (** uninterpreted symbol *)
    | Def of id * 'ty * 'term (** defined symbol *)
    | Axiom of 'term

  type ('a, 'b) t = {
    view: ('a, 'b) view;
    loc: Loc.t option;
  }

  let view t = t.view
  let loc t = t.loc

  let make_ ?loc view = {loc;view}

  let decl ?loc v t = make_ ?loc (Decl (v,t))
  let def ?loc v ~ty t = make_ ?loc (Def (v,ty,t))
  let axiom ?loc t = make_ ?loc (Axiom t)

  let map ~term:ft ~ty:fty st =
    let loc = st.loc in
    match st.view with
    | Decl (id,ty) -> decl ?loc id (fty ty)
    | Def (id,ty,t) -> def ?loc id ~ty:(fty ty) (ft t)
    | Axiom t -> axiom ?loc (ft t)

  let print pt pty out t =
    match t.view with
    | Decl (v, ty) -> fpf out "@[<2>val %a@ : %a.@]" ID.print v pty ty
    | Def (v, ty, t) ->
        fpf out "@[<2>def %a@ : %a@ := %a.@]"
          ID.print v pty ty pt t
    | Axiom t -> fpf out "@[<2>axiom %a.@]" pt t

  let print_list pt pty out l =
    fpf out "@[<v>%a@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" (print pt pty)) l
end

module Signature = struct
  type 'ty t = 'ty NunID.Map.t

  let empty = ID.Map.empty
end

type ('t, 'ty) t = {
  statements : ('t, 'ty) Statement.t list;
  signature : 'ty Signature.t lazy_t; (* id -> type *)
  defs : 't NunID.Map.t lazy_t; (* id -> definition *)
}

let make ?(signature=lazy Signature.empty) ?(defs=lazy ID.Map.empty) statements =
  { statements; signature; defs }

let statements t = t.statements

let signature t = Lazy.force t.signature

let defs t = Lazy.force t.defs

(* XXX print signature too? *)
let print pt pty out problem =
  fpf out "@[<v2>{%a}@]"
    (Statement.print_list pt pty) problem.statements

module Model = struct
  type 't t = ('t * 't) list

  let map ~f m = CCList.map (fun (x,y) -> f x, f y) m

  let print pt out m =
    let pp_pair out (t,u) = fpf out "@[<hv2>%a ->@ %a@]" pt t pt u in
    Format.fprintf out "@[<v>%a@]"
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" pp_pair) m
end
