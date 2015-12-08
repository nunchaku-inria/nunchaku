
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to CVC4} *)

module Make(F : FO.S) : sig
  include Solver_intf.S
  with module FO_T = F
  and module FOBack = FO.Default

  val print_problem : Format.formatter -> problem -> unit

  val solve_par :
    ?j:int -> ?options:string list -> ?timeout:float -> ?print:bool ->
    problem -> FOBack.T.t Solver_intf.Res.t
  (** Version of {!solve} that tries different sets of options in parallel *)
end

type model_elt = FO.Default.T.t

exception CVC4_error of string

(** list of different available options *)
val options_l : string list

(** Call CVC4 on a problem and obtain a result
  @param options: flags to pass the solver. If several strings are passed,
    they are tried one by one until the deadline is reached or the solver
    returns "SAT"
  @raise Invalid_argument if options=[]
  @raise CVC4_error if the solver failed with an error
*)
val call :
  (module FO.S with type T.t = 't and type Ty.t = 'ty) ->
  ?options:string list ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('t, 'ty) FO.Problem.t ->
  model_elt Problem.Res.t

(** Close a pipeline by calling CVC4
  @param print if true, print the input problem
  @param print_smt if true, print the SMT problem sent to the prover
  @param deadline absolute time at which the solver should stop (even without an answer)
  @param options list of options to try. IF several options are provided,
    the deadline will still be respected.
  @raise CVC4_error if the solver failed with an error
*)
val close_pipe :
  (module FO.S with type T.t = 't and type Ty.t = 'ty) ->
  ?options:string list ->
  pipe:('d, ('t, 'ty) FO.Problem.t, 'e, 'f) Transform.Pipe.t ->
  print:bool ->
  print_smt:bool ->
  deadline:float ->
  ('d, 'e, 'f, model_elt Problem.Res.t) Transform.ClosedPipe.t
