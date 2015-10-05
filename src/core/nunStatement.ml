
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

module Loc = NunLocation
module ID = NunID

type loc = Loc.t
type id = ID.t

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

type 'a printer = Format.formatter -> 'a -> unit

let fpf = Format.fprintf

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
