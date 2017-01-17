
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Conversion HO/FO} *)

open Nunchaku_core

module Of_ho(T_ho : TermInner.S) : sig
  exception NotInFO of string

  val convert_problem :
    (T_ho.t,T_ho.t) Problem.t ->
    (FO.T.t,FO.Ty.t) FO.Problem.t
    (** Conversion of problem from HO to FO
        @raise NotInFO if some constructs are not translatable *)
end

module To_ho(T_ho : TermInner.S) : sig
  val convert_ty : FO.Ty.t -> T_ho.t

  val convert_term : FO.T.t -> T_ho.t

  val convert_model : (FO.T.t, FO.Ty.t) Model.t -> (T_ho.t,T_ho.t) Model.t
end

module Make(T1 : TermInner.S) : sig
  val pipe_with :
    print:bool ->
    decode:(unit -> 'a -> 'b) ->
    ((T1.t, T1.t) Problem.t, (FO.T.t, FO.Ty.t) FO.Problem.t,
     'a, 'b)
      Transform.transformation

  val pipe :
    print:bool ->
    unit ->
    ((T1.t, T1.t) Problem.t, (FO.T.t, FO.Ty.t) FO.Problem.t,
     (FO.T.t, FO.Ty.t) FO.res, (T1.t, T1.t) FO.res)
      Transform.transformation
end
