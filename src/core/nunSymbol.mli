
(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Symbol} *)

type t
(** A symbol, that is, a string *)

include NunIntf.EQ with type t := t
include NunIntf.ORD with type t := t
include NunIntf.HASH with type t := t

val make : string -> t
(** [make s] creates a symbol with name [s]. If such a symbol already
    exists, it is returned. *)

include NunIntf.PRINT with type t := t
(**  Pretty printing *)

val to_string : t -> string



