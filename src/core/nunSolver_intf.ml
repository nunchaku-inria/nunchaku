
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Interface to ground SMT solvers} *)

module ID = NunID
module Var = NunVar

module FO = NunFO.Default
module T = FO.T
module Ty = FO.Ty
module F = FO.Formula

type id = ID.t
type 'a var = 'a Var.t

type term = T.t
type ty = Ty.t
type toplevel_ty = Ty.arrow
type formula = F.t

(** {2 The Problems sent to Solvers} *)
module Problem = struct

  (* TODO: add a type declaration (create new type, such as "nat") *)

  (** One top-level statement of the problem *)
  type statement =
    | TyDecl of id * int  (** number of arguments *)
    | Decl of id * toplevel_ty
    | Def of id * toplevel_ty * term
    | FormDef of id * formula
    | Axiom of formula

  type t = {
    statements: statement list;
  }
end

(** {2 A Ground Model} *)
module Model = struct
  type t = {
    get_values: id list -> (id * term) list
  }
end

module Res = struct
  type t =
    | Sat of Model.t
    | Unsat
    | Timeout
    | Error of string
end

exception SolverClosed

(** {2 The Interface of a Solver} *)
module type S = sig
  type t
  (** An instance of the solver *)

  val name : string
  (** Name of the solver *)

  val res : t -> Res.t
  (** [res s] blocks until the result of [s] is available, then return it *)

  val peek_res : t -> Res.t option
  (** [peek_res s] checks whether the result of [s] is already available *)

  val solve : ?timeout:float -> Problem.t -> t
  (** [solve problem] creates a new solver and sends it the given problem.
      This function should return immediately, without waiting for the solver
      to return with an answer.

      The answer can be peeked at using {!peek_res}, or obtained through a
      blocking call to {!res}.

      @param timeout the number of seconds given, at most, to the solver.
        There is a default timeout, so if you want the solver to run forever
        you should give something like [timeout = 1e10] *)

  val close : t -> unit
  (** [close s] releases resources used by [s], and makes every operation
      called on [s] (except [close s]) allowed to raise SolverClosed from now on.
      In particular it might not be possible to use the model obtained
      from [s] after calling [close s]. *)
end



