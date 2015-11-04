
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Flatten pattern-matching in Equations} *)

module Make(T : NunTerm_ho.S) : sig

  val pipe :
    print:bool ->
      (('i T.t, 'i T.t, [`Nested]) NunProblem.t,
      ('i T.t, 'i T.t, [`Linear]) NunProblem.t,
      'b, 'b
    ) NunTransform.t
  (** Pipeline component. Reverse direction is identity. *)
end
