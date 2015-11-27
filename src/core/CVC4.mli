
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module Make(F : FO.VIEW) : sig
  include Solver_intf.S
  with module FO_T = F
  and module FOBack = FO.Default

  val print_problem : Format.formatter -> problem -> unit
end

type model_elt = FO.Default.term_or_form

(** Call CVC4 on a problem and obtain a result *)
val call :
  (module FO.VIEW with type formula = 'a and type T.t = 'b and type Ty.t = 'c) ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('a, 'b, 'c) FO.Problem.t ->
  model_elt Problem.Res.t

(** Close a pipeline by calling CVC4 *)
val close_pipe :
  (module FO.VIEW with type formula = 'a and type T.t = 'b and type Ty.t = 'c) ->
  pipe:('d, ('a, 'b, 'c) FO.Problem.t, 'e, 'f) Transform.Pipe.t ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('d, 'e, 'f, model_elt Problem.Res.t) Transform.ClosedPipe.t
