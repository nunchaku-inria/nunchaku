(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Model} *)

type 'a printer = Format.formatter -> 'a -> unit

type 't t = {
  terms: ('t * 't) list;  (* term -> its interpretation *)
  finite_types: ('t * 't list) list;  (* type -> finite domain *)
}

val empty : 'a t
(** Empty model *)

val make : ?finite_types:('t * 't list) list -> ('t * 't) list -> 't t

val add : 'a t -> 'a * 'a -> 'a t
(** Add a term interpretation *)

val add_finite_type : 'a t -> 'a -> 'a list -> 'a t
(** Map the type to its finite domain. *)

val iter :
  terms:('a * 'a -> unit) ->
  finite_types:('a * 'a list -> unit) ->
  'a t ->
  unit

val filter_map :
  terms:('a * 'a -> ('b * 'b) option) ->
  finite_types:('a * 'a list -> ('b * 'b list) option) ->
  'a t ->
  'b t

val map : f:('a -> 'b) -> 'a t -> 'b t

val print : 't printer -> 't t printer
