
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Terms with Types} *)

module Make(Ty : NunTypeInference.TYPE) :
  NunTypeInference.TERM with module Ty = Ty

