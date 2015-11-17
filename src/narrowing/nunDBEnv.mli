
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Environment for De Bruijn indices} *)

type +'a t = private {
  len : int;
  lst : 'a list;
}

val cons : 'a -> 'a t -> 'a t
val cons_l : 'a list -> 'a t -> 'a t
val nil : 'a t
val is_empty : _ t -> bool
val length : _ t -> int

val to_list : 'a t -> 'a list
val of_list : 'a list -> 'a t

val make : len:int -> 'a list -> 'a t
val make_unsafe : len:int -> 'a list -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t
val append_l : 'a t -> 'a list -> 'a t
val for_all : ('a -> bool) -> 'a t -> bool
val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
val remove : int -> 'a t -> 'a t
val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val nth : 'a t -> int -> 'a
