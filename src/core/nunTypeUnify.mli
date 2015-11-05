
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

type 'a sequence = ('a -> unit) -> unit

type ('t,'inv) repr = ('t,'inv) NunType_intf.repr

type 'inv_p invariant = <poly: 'inv_p; meta: NunMark.with_meta>
(** Invariant: must have meta-variables *)

exception Fail of (NunType_intf.packed * NunType_intf.packed) list * string
(** Raised when unification fails. The list of pairs of types is the
    unification stack (with the innermost types first) *)

val unify_exn : repr:('t, _ invariant) repr -> 't -> 't -> unit
(** Unify the two types, modifying their binding in place.
    @raise Fail if the types are not unifiable *)

type 't meta_vars_set = 't NunMetaVar.t NunID.Map.t
(* a set of meta-variable with their reference *)

val free_meta_vars :
  repr:('t, _ invariant) repr ->
  ?init:'t meta_vars_set ->
  't ->
  't meta_vars_set
(** Compute the set of free meta variables that can be bound,
    mapped to their meta-variable *)

