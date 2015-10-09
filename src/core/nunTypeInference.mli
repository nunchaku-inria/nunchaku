
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

type 'a or_error = [`Ok of 'a | `Error of string]
type id = NunID.t
type 'a var = 'a NunVar.t
type loc = NunLocation.t

exception ScopingError of string * string * loc option
(** Scoping error for the given variable *)

(** {2 Typed Term} *)
module type TERM = NunTerm_typed.S

(** {2 Type Inference/Checking}

  Functions exposed by this functor will mutate in place their input,
  by calling [Term.Ty.bind]. *)

type attempt_stack = NunUntypedAST.term list
(** a trace of inference attempts with a message and optional location
    for each attempt. *)

exception TypeError of string * attempt_stack
(** Raised when the input is ill-typed or could not be inferred. *)

module Convert(Term : TERM) : sig
  type env

  val empty_env : env

  val convert_ty : env:env -> NunUntypedAST.ty -> Term.Ty.t or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_ty_exn : env:env -> NunUntypedAST.ty -> Term.Ty.t
  (** @raise ScopingError if the type isn't well-scoped *)

  val convert_term : env:env -> NunUntypedAST.term -> Term.t or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_term_exn : env:env -> NunUntypedAST.term -> Term.t
  (** Unsafe version of {!convert}
      @raise TypeError if it fails to  type properly *)

  val generalize : Term.t -> Term.t * Term.Ty.t var list
  (** Generalize a term [t] by parametrizing it over its free {b type}
      variables.
      @return a pair [(t', vars)] such that, roughly, [app t' vars = t] *)

  type statement = (Term.t, Term.Ty.t) NunProblem.Statement.t

  val convert_statement : env:env -> NunUntypedAST.statement -> (statement * env) or_error

  val convert_statement_exn : env:env -> NunUntypedAST.statement -> statement * env
  (** Unsafe version of {!convert} *)

  type problem = (Term.t, Term.Ty.t) NunProblem.t

  val convert_problem : env:env -> NunUntypedAST.statement list -> (problem * env) or_error

  val convert_problem_exn : env:env -> NunUntypedAST.statement list -> problem * env
end

(** Pipeline component. Takes input and output Term representations. *)
val pipe :
  print:bool ->
  (module NunTerm_typed.S with type t = 'a) ->
  (module NunTerm_ho.S with type t = 'b) ->
  (NunUntypedAST.statement list, ('a, 'a) NunProblem.t,
    'b NunProblem.Model.t, NunUntypedAST.term NunProblem.Model.t)
    NunTransform.t
