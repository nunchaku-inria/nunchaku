
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

type var = NunVar.t
type 'a sequence = ('a -> unit) -> unit

module Make(Ty : NunType_intf.UNIFIABLE) : sig
  exception Fail of (Ty.t * Ty.t) list * string
  (** Raised when unification fails. The list of pairs of types is the
      unification stack (with the innermost types first) *)

  val unify_exn : Ty.t -> Ty.t -> unit
  (** Unify the two types, modifying their binding in place.
      @raise Fail if the types are not unifiable *)

  val deref_rec : Ty.t -> Ty.t
  (** Dereference recursively [ty] if [ty] is a variable bound to another
      type *)

  val free_vars : ?init:NunVar.Set.t -> Ty.t -> NunVar.Set.t
  (** Compute the set of free variables *)

  val eval : Ty.t -> Ty.t
  (** Fully evaluate all variables of the given type *)
end


