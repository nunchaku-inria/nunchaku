
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

module Make(T : TermInner.S) : sig
  val whnf : T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

  type subst = (T.t,T.t) Var.Subst.t

  val app_whnf : ?subst:subst -> T.t -> T.t list -> T.t
  (** [app_whnf f l] applies [f] to [l], then computes the weak head normal form *)

  module Full : sig
    val whnf : ?subst:subst-> T.t -> T.t list -> (T.t * T.t list * subst)
  end
end
