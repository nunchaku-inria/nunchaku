
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Constant} *)

type id = NunID.t
type 'a var = 'a NunVar.t
type 'a printer = Format.formatter -> 'a -> unit

type 'term t = private {
  id: id; (* symbol *)
  ty: 'term; (* type of symbol *)
  mutable def: 'term def; (* definition/declaration for the symbol *)
}

and 'term def =
  | Cstor of 'term datatype Lazy.t (* map of all other constructors *)

  | Def of 'term (* id == rhs *)

  | Datatype of 'term datatype Lazy.t

  | Opaque
  (* TODO: DefNode of term * node, for memoization *)

and 'term datatype = {
  ty_kind: [`Data | `Codata];
  ty_id: id; (* type being defined *)
  ty_n_vars: int;  (* number of type variables *)
  ty_cstors: 'term t NunID.Map.t; (* constructors *)
}

val is_cstor : _ t -> bool
val is_def : _ t -> bool

val make : def:'term def -> ty:'term -> id -> 'term t
val set_ty : 'term t -> ty:'term -> 'term t

val print : 'a t printer
val print_full : 'a printer -> 'a t printer
