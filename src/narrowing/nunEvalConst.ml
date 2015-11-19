
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Constant} *)

module ID = NunID

type id = NunID.t

type 'term t = {
  id: id; (* symbol *)
  ty: 'term; (* type of symbol *)
  mutable def: 'term def; (* definition/declaration for the symbol *)
}
and 'term def =
  | Cstor of
      'term (* the datatype *)
      * 'term t list (* list of all constructors *)

  | Def of 'term (* id == this term *)

  | Datatype of
      [`Data | `Codata]
      * 'term t list (* list of constructors *)

  | Opaque

let is_cstor c = match c.def with Cstor _ -> true | _ -> false
let is_def c = match c.def with Def _ -> true | _ -> false

let make ~def ~ty id = {def; ty; id}
let set_ty t ~ty = {t with ty; }

