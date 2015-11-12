
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

type 'a sequence = ('a -> unit) -> unit

module Make(T : NunTypePoly.REPR) : sig
  exception Fail of (T.t * T.t) list * string
  (** Raised when unification fails. The list of pairs of types is the
      unification stack (with the innermost types first) *)

  val unify_exn : T.t -> T.t -> unit
  (** Unify the two types, modifying their binding in place.
      @raise Fail if the types are not unifiable *)

  type meta_vars_set = T.t NunMetaVar.t NunID.Map.t
  (* a set of meta-variable with their reference *)

  val free_meta_vars : T.t -> meta_vars_set
  (** Compute the set of free meta variables that can be bound,
      mapped to their meta-variable *)
end
