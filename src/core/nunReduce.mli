
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

(* TODO: delta-reduction (expand definitions of Const) *)

type ('t, 'inv) build = ('t, 'inv) NunTerm_ho.build

val whnf : build:('t, _) build -> 't -> 't
(** Weak Head Normal Form *)

val snf : build:('t, _) build -> 't -> 't
(** Strong Normal Form (reduce under functions) *)

module Full : sig
  type 't subst = ('t,'t) NunVar.Subst.t

  (* TODO: expose the internal "state" record? *)

  val whnf :
    build:('t, _) build ->
    ?subst:'t subst->
    't ->
    't list ->
    ('t * 't list * 't subst)
end
