
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Reductions, including Beta Reduction} *)

module Make(T : NunTypeInference.TERM) : sig

  val whnf : T.t -> T.t
  (** Weak Head Normal Form *)

  val snf : T.t -> T.t
  (** Strong Normal Form (reduce under functions) *)

end
