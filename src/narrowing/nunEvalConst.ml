
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Constant} *)

module ID = NunID

type 'a var = 'a NunVar.t
type id = NunID.t
type 'a printer = Format.formatter -> 'a -> unit

type 'term t = {
  id: id; (* symbol *)
  ty: 'term; (* type of symbol *)
  mutable def: 'term def; (* definition/declaration for the symbol *)
}

and 'term def =
  | Cstor of 'term datatype Lazy.t (* map of all other constructors *)

  | Def of 'term (* id == fun vars -> rhs *)

  | Datatype of 'term datatype Lazy.t

  | Opaque

and 'term datatype = {
  ty_kind: [`Data | `Codata];
  ty_id: id; (* type being defined *)
  ty_n_vars: int;  (* number of type variables *)
  ty_cstors: 'term t NunID.Map.t; (* constructors *)
}

let is_cstor c = match c.def with Cstor _ -> true | _ -> false
let is_def c = match c.def with Def _ -> true | _ -> false

let make ~def ~ty id = {def; ty; id}
let set_ty t ~ty = {t with ty; }

let print out c = ID.print_name out c.id

let print_full ppt out c =
  let fpf = Format.fprintf in
  let ppcstors out d =
    CCFormat.list print out (ID.Map.to_list d.ty_cstors |> List.map snd) in
  let ppdef out = function
    | Opaque -> ()
    | Cstor (lazy d) -> fpf out " := cstor %a" ppcstors d
    | Datatype (lazy d) -> fpf out " := datatype %a" ppcstors d
    | Def t -> fpf out " := `@[%a@]`" ppt t
  in
  fpf out "@[<2>%a:%a@,%a@]" ID.print_name c.id ppt c.ty ppdef c.def

