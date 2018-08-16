
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

module type S = sig
  type term

  type subst = (term,term) Var.Subst.t

  val whnf : ?subst:subst -> term -> term
  (** Weak Head Normal Form *)

  val snf : ?subst:subst -> term -> term
  (** Strong Normal Form (reduce under functions) *)

  val app_whnf : ?subst:subst -> term -> term list -> term
  (** [app_whnf f l] applies [f] to [l], then computes the weak head normal form *)

  val eta_reduce : term -> term
  (** Eta-reduction at the root of the term.
      This replaces [λx. f x] with [f], if [f] does not contain [x] *)

  module Full : sig
    val whnf :
      ?subst:subst ->
      term ->
      term list ->
      (term * term list * subst * term Builtin.guard)
      (** [whnf f l] applies [f] to [l] and returns its WHNF, as a tuple
          [f', l', subst, guard] where
          [f l ---> subst ((f guard) l)] *)
  end
end

module Make(T : TermInner.FULL) : S with type term := T.t
