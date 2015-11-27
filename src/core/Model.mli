(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Model} *)

type 'a printer = Format.formatter -> 'a -> unit

type 't t = ('t * 't) list

val map : f:('a -> 'b) -> 'a t -> 'b t

val print : 't printer -> 't t printer
