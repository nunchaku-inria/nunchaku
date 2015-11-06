
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

type ('t, 'inv) build = ('t, 'inv) NunTerm_ho.build

module Make(T : NunTerm_ho.BUILD) : sig
  val whnf : 'inv T.t -> 'inv T.t
  (** Weak Head Normal Form *)

  val snf : 'inv T.t -> 'inv T.t
  (** Strong Normal Form (reduce under functions) *)

  module Full : sig
    type 't subst = ('t,'t) NunVar.Subst.t

    (* TODO: expose the internal "state" record? *)

    val whnf :
      ?subst:'inv T.t subst->
      'inv T.t ->
      'inv T.t list ->
      ('inv T.t * 'inv T.t list * 'inv T.t subst)
  end
end
