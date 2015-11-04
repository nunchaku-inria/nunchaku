
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Feature Markers}

  Let the feast of a thousand GADTs begin! *)

(** Polymorphic/monomorphic types *)

type polymorph = M_polymorph
type monomorph = M_monomorph

type _ poly_witness =
  | Poly : polymorph poly_witness
  | Mono : monomorph poly_witness

(** Terms with/without meta-variables *)

type with_meta = M_with_meta
type without_meta = M_without_meta

(** Equations with/without pattern matching *)

type linear = M_linear (* forall x, f x = ... *)
type nested = M_nested (* forall ..., f pattern = ... *)
