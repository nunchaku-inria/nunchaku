
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Make(T : NunTerm_ho.S)(Subst : NunVar.SUBST with type ty = T.ty) : sig

  (* TODO: delta-reduction (expand definitions of Const) *)

  val whnf : T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

  module Full : sig
    type subst = T.t Subst.t

    val whnf :
      ?subst:subst->
      T.t ->
      T.t list ->
      (T.t * T.t list * subst)
  end
end
