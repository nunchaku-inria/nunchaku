
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

open Nunchaku_core

type 'a or_error = [`Ok of 'a | `Error of string]
type id = ID.t
type 'a var = 'a Var.t
type loc = Location.t

type stmt_invariant = <ty:[`Poly]; eqn:[`Nested]; ind_preds:[`Present]>

exception ScopingError of string * string * loc option
(** Scoping error for the given variable *)

(** {2 Type Inference/Checking}

  Functions exposed by this functor will mutate in place their input,
  by calling [Term.Ty.bind]. *)

type attempt_stack = UntypedAST.term list
(** a trace of inference attempts with a message and optional location
    for each attempt. *)

exception TypeError of string * attempt_stack
(** Raised when the input is ill-typed or could not be inferred. *)

module Convert(T : TermTyped.S) : sig
  type term = T.t
  type env

  val empty_env : env
  (** Make a new, empty environment. The build function will be used
      to construct new terms *)

  val convert_ty : env:env -> UntypedAST.ty -> term or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_ty_exn : env:env -> UntypedAST.ty -> term
  (** @raise ScopingError if the type isnT.t well-scoped *)

  val convert_term : env:env -> UntypedAST.term -> term or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_term_exn : env:env -> UntypedAST.term -> term
  (** Unsafe version of {!convert}
      @raise TypeError if it fails to  type properly *)

  val generalize : close:[`Forall | `Fun | `NoClose] ->
                   term -> term * term var list
  (** Generalize a T.t [t] by parametrizing it over its free {b type}
      variables.
      @param close decides how [t] is generalized
        {ul
          {- [`Forall] makes [t' = forall vars t]}
          {- [`Fun] makes [t' = fun vars t]}
          {- [`NoClose] makes [t' = t] with meta variables replaced by [vars]}
        }
      @return a pair [(t', vars)] such that, roughly, [app t' vars = t],
        or [t'] is [forall vars t], or [t'] contains [vars] *)

  type statement = (term, term, stmt_invariant) Statement.t

  val read_prelude : env:env -> statement list * env
  (** Add the prelude to [env] and return the corresponding statements and
      new environment.
      Called automatically in {!convert_problem} and {!convert_problem_exn}. *)

  val convert_statement :
    env:env ->
    UntypedAST.statement ->
    (statement * env) or_error

  val convert_statement_exn :
    env:env ->
    UntypedAST.statement ->
    statement * env
  (** Unsafe version of {!convert} *)

  type problem = (term, term, stmt_invariant) Problem.t

  val convert_problem :
    env:env ->
    UntypedAST.statement CCVector.ro_vector ->
    (problem * env) or_error

  val convert_problem_exn :
    env:env ->
    UntypedAST.statement CCVector.ro_vector ->
    problem * env
end

module Make(T1 : TermTyped.S)(T2 : TermInner.S) : sig
  type term1 = T1.t
  type term2 = T2.t

  val pipe :
    print:bool ->
    (UntypedAST.statement CCVector.ro_vector,
      (term1, term1, stmt_invariant) Problem.t, 'a, 'a)
      Transform.t
  (** Pipeline component. Takes input and output Term representations. *)

  val pipe_with :
    decode:('c -> 'd) ->
    print:bool ->
    (UntypedAST.statement CCVector.ro_vector,
      (term1, term1, stmt_invariant) Problem.t, 'c, 'd)
    Transform.t
end
