
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Make(T : NunTerm_ho.S) : sig

  (* TODO: delta-reduction (expand definitions of Const) *)

  val whnf : T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

end
