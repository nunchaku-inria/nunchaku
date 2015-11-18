
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Constant} *)

type id = NunID.t

type 'term t = private {
  id: id; (* symbol *)
  ty: 'term; (* type of symbol *)
  mutable def: 'term def; (* definition/declaration for the symbol *)
}
and 'term def =
  | Cstor of
      'term (* the datatype *)
      * 'term t list (* list of all constructors *)

  | Def of 'term (* id == this term *)

  | Overload of
      ('term * 'term def) list
      (* decision tree based on the first (type) argument:
        each [arg,def'] in the list means that [id arg = def'] *)

  | Datatype of
      [`Data | `Codata]
      * 'term t list (* list of constructors *)

  | Opaque
  (* TODO: DefNode of term * node, for memoization *)

val is_cstor : _ t -> bool
val is_def : _ t -> bool

val make : def:'term def -> ty:'term -> id -> 'term t

exception Invalid of string

val add_def : 'term t -> args:'term list -> 'term -> unit
(** [add_def const ~args t] assumes that [const.def] is [Opaque] or [Overload],
    and adds [args -> t] as an overloaded definition *)


