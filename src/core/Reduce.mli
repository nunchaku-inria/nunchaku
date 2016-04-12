
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

module Make(T : TermInner.S) : sig
  type subst = (T.t,T.t) Var.Subst.t

  val whnf : ?subst:subst -> T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : ?subst:subst -> T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

  val app_whnf : ?subst:subst -> T.t -> T.t list -> T.t
  (** [app_whnf f l] applies [f] to [l], then computes the weak head normal form *)

  val eta_reduce : T.t -> T.t
(** Eta-reduction at the root of the term.
    This replaces [λx. f x] with [f], if [f] does not contain [x] *)

  module Full : sig
    val whnf : ?subst:subst-> T.t -> T.t list -> (T.t * T.t list * subst)
  end
end
