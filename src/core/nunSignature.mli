(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Signature}

  Maps symbols to their type *)

type id = NunID.t

type 'ty t = 'ty NunID.Map.t

val empty : _ t

val mem : sigma:'a t -> id -> bool
val find : sigma:'a t -> id -> 'a option
val find_exn : sigma:'a t -> id -> 'a (** @raise Not_found if not present *)

val declare : sigma:'a t -> id -> 'a -> 'a t
