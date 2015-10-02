
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Statements with Locations} *)

type loc = NunLocation.t
type var = NunVar.t

include NunStatement_intf.S

val loc : (_,_) t -> loc option

val decl : ?loc:loc -> var -> 'a -> (_, 'a) t
val def : ?loc:loc -> var -> 'a -> ('a, _) t
val axiom : ?loc:loc -> 'a -> ('a,_) t

type 'a printer = Format.formatter -> 'a -> unit

val print : 'a printer -> 'b printer -> ('a,'b) t printer

val print_list : 'a printer -> 'b printer -> ('a,'b) t list printer
