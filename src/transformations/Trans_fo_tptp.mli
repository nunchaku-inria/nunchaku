
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Translation FO/FO_tptp} *)

open Nunchaku_core

(** Assume there are no types (other than `Unitype), no datatypes, no
    pattern match... *)
module To_tptp : sig
  exception Error of string

  val conv_form : FO.T.t -> FO_tptp.form
  (** @raise Error if conversion failed *)

  val conv_statement : (FO.T.t, FO.Ty.t) FO.statement -> FO_tptp.statement option
  (** convert the statement. Some statements will just disappear (mostly,
      declarations).
      @raise Error if conversion failed *)

  val conv_problem : (FO.T.t, FO.Ty.t) FO.Problem.t -> FO_tptp.problem
end

module Of_tptp : sig
  val conv_ty : FO_tptp.ty -> FO.Ty.t
  val conv_term : FO_tptp.term -> FO.T.t
  val conv_form : FO_tptp.form -> FO.T.t
end

val pipe :
  ((FO.T.t, FO.Ty.t) FO.Problem.t, FO_tptp.problem,
   (FO_tptp.term, FO_tptp.ty) FO.res,
   (FO.T.t, FO.Ty.t) FO.res) Transform.t
