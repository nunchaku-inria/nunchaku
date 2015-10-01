
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Unification of Types} *)

module Make(Ty : NunType_intf.UNIFIABLE) : sig

  exception Fail of Ty.t * Ty.t * string
  
  val unify_exn : Ty.t -> Ty.t -> unit
  (** Unify the two types, modifying their binding in place.
      @raise Fail if the types are not unifiable *)

  val eval : Ty.t -> Ty.t
  (** Fully evaluate all variables of the given type *)
end


