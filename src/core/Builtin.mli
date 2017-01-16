
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Builtins}

    A builtin is a special construct of Nunchaku *)

type id = ID.t

type 'a guard = {
  asserting : 'a list;
}

val empty_guard : 'a guard

val map_guard : ('a -> 'b) -> 'a guard -> 'b guard

val merge_guard : 'a guard -> 'a guard -> 'a guard

val pp_guard : 'a CCFormat.printer -> 'a guard CCFormat.printer

type 'a t =
  [ `And of 'a list
  | `DataSelect of id * int
  | `DataTest of id
  | `Eq of 'a * 'a
  | `False
  | `Guard of 'a * 'a guard
  | `Imply of 'a * 'a
  | `Ite of 'a * 'a * 'a
  | `Not of 'a
  | `Or of 'a list
  | `True
  | `Undefined_atom of id * 'a
  | `Undefined_self of id * 'a
  | `Unparsable of 'a ]

val prec : 'a t -> Precedence.t

val print_infix_list :
  'a CCFormat.printer ->
  string ->
  'a list CCFormat.printer

val pp : 'a CCFormat.printer -> 'a t CCFormat.printer

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val map : f:('a -> 'b) -> 'a t -> 'b t

val fold : f:('acc -> 'a -> 'acc) -> x:'acc -> 'a t -> 'acc

val fold2_l :
  f:('a -> 'b -> 'c -> 'a) ->
  fail:(unit -> 'a) -> x:'a -> 'b list -> 'c list -> 'a

val fold2 :
  f:('acc -> 'a -> 'b -> 'acc) ->
  fail:(unit -> 'acc) -> x:'acc -> 'a t -> 'b t -> 'acc

val iter : ('a -> unit) -> 'a t -> unit

val to_seq : 'a t -> ('a -> unit) -> unit

val to_sexp : ('a -> Sexp_lib.t) -> 'a t -> Sexp_lib.t

