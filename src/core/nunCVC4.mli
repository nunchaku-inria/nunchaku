
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module Make(FO : NunFO.VIEW) : sig
  include NunSolver_intf.S
  with module FO = FO
  and module FOBack = NunFO.Default

  val print_problem : Format.formatter -> problem -> unit
end

type model_elt = NunFO.Default.term_or_form

(** Call CVC4 on a problem and obtain a result *)
val call :
  (module NunFO.VIEW with type formula = 'a and type T.t = 'b and type Ty.t = 'c) ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('a, 'b, 'c) NunFO.Problem.t ->
  model_elt NunProblem.Res.t

(** Close a pipeline by calling CVC4 *)
val close_pipe :
  (module NunFO.VIEW with type formula = 'a and type T.t = 'b and type Ty.t = 'c) ->
  pipe:('d, ('a, 'b, 'c) NunFO.Problem.t, 'e, 'f) NunTransform.Pipe.t ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('d, 'e, 'f, model_elt NunProblem.Res.t) NunTransform.ClosedPipe.t
