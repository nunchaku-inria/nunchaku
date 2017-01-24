
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encode Cardinality Constraints into Formulas} *)

(** If we have some constraint [max_card ty = 3], we add an axiom
    [exists a b c : ty.
      forall x:ty. (x = a || x = b || x = c)]

    Similarly we can encode minimum cardinality [max_card ty = 3] into:
    [exists a b c: ty. distinct(a,b,c)]
*)

module type S = sig
  module T : TermInner.S

  type term = T.t
  type ty = T.t

  val encode_max_card : ty -> int -> term

  val encode_min_card : ty -> int -> term
end

module Make(T : TermInner.S) : S with module T = T
