
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to ground SMT solvers} *)

module ID = ID
module Var = Var

type id = ID.t
type 'a var = 'a Var.t

module Res = struct
  type 't t =
    | Sat of 't Model.t
    | Unsat
    | Timeout
    | Error of string
end

exception SolverClosed
(** Raised when the solver has been stopped (see {!S.close}) and some
    function is invoked on it *)

(** {2 The Interface of a Solver} *)
module type S = sig
  module FO_T : FO.VIEW (* input terms *)
  module FOBack : FO.S (* output terms (in the model) *)

  type problem = (FO_T.Formula.t, FO_T.T.t, FO_T.Ty.t) FO.Problem.t

  type t
  (** An instance of the solver *)

  val name : string
  (** Name of the solver *)

  val res : t -> FOBack.term_or_form Res.t
  (** [res s] blocks until the result of [s] is available, then return it *)

  val peek_res : t -> FOBack.term_or_form Res.t option
  (** [peek_res s] checks whether the result of [s] is already available *)

  val solve : ?options:string -> ?timeout:float -> ?print:bool -> problem -> t
  (** [solve problem] creates a new solver and sends it the given problem.
      This function should return immediately, without waiting for the solver
      to return with an answer.

      The answer can be peeked at using {!peek_res}, or obtained through a
      blocking call to {!res}.

      @param options additional options to pass the solver
      @param print if true, the solver should print its input on stdout
      @param timeout the number of seconds given, at most, to the solver.
        There is a default timeout, so if you want the solver to run forever
        you should give something like [timeout = 1e10] *)

  val close : t -> unit
  (** [close s] releases resources used by [s], and makes every operation
      called on [s] (except [close s]) allowed to raise SolverClosed from now on.
      In particular it might not be possible to use the model obtained
      from [s] after calling [close s]. *)
end


(**/**)

let print_model_ = ref false
(** If true, solver interfaces might print the raw model before parsing it *)

(**/**)


