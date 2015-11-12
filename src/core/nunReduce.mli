
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

module Make(T : NunTermInner.S) : sig
  val whnf : T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

  module Full : sig
    type subst = (T.t,T.t) NunVar.Subst.t

    (* TODO: expose the internal "state" record? *)

    val whnf : ?subst:subst-> T.t -> T.t list -> (T.t * T.t list * subst)
  end
end
