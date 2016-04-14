
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lazy List} *)

type +'a t = 'a cell lazy_t
and +'a cell =
  | Nil
  | Cons of 'a * 'a t

val empty : 'a t

val return : 'a -> 'a t

val is_empty : _ t -> bool

val cons : 'a -> 'a t -> 'a t

val head : 'a t -> ('a * 'a t) option

val map : f:('a -> 'b) -> 'a t -> 'b t

val append : 'a t -> 'a t -> 'a t

module Infix : sig
  val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

include module type of Infix

type 'a gen = unit -> 'a option

val of_gen : 'a gen -> 'a t

val of_list : 'a list -> 'a t

val to_list : 'a t -> 'a list

val to_list_rev  : 'a t -> 'a list
