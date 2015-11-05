
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

type 'a or_error = [`Ok of 'a | `Error of string]
type id = NunID.t
type 'a var = 'a NunVar.t
type 'a signature = 'a NunSignature.t
type loc = NunLocation.t

type stmt_invariant = NunMark.nested

exception ScopingError of string * string * loc option
(** Scoping error for the given variable *)

(** {2 Type Inference/Checking}

  Functions exposed by this functor will mutate in place their input,
  by calling [Term.Ty.bind]. *)

type attempt_stack = NunUntypedAST.term list
(** a trace of inference attempts with a message and optional location
    for each attempt. *)

exception TypeError of string * attempt_stack
(** Raised when the input is ill-typed or could not be inferred. *)

module Convert : sig
  type 't env

  val empty_env : build:'t NunTerm_typed.build -> 't env
  (** Make a new, empty environment. The build function will be used
      to construct new terms *)

  val signature : 't env -> 't signature

  val convert_ty : env:'t env -> NunUntypedAST.ty -> 't or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_ty_exn : env:'t env -> NunUntypedAST.ty -> 't
  (** @raise ScopingError if the type isn't well-scoped *)

  val convert_term : env:'t env -> NunUntypedAST.term -> 't or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_term_exn : env:'t env -> NunUntypedAST.term -> 't
  (** Unsafe version of {!convert}
      @raise TypeError if it fails to  type properly *)

  val generalize : close:[`Forall | `Fun | `NoClose] ->
                   't -> 't * 't var list
  (** Generalize a term [t] by parametrizing it over its free {b type}
      variables.
      @param close decides how [t] is generalized
        {ul
          {- [`Forall] makes [t' = forall vars t]}
          {- [`Fun] makes [t' = fun vars t]}
          {- [`NoClose] makes [t' = t] with meta variables replaced by [vars]}
        }
      @return a pair [(t', vars)] such that, roughly, [app t' vars = t],
        or [t'] is [forall vars t], or [t'] contains [vars] *)

  type 't statement = ('t, 't, stmt_invariant) NunStatement.t

  val convert_statement :
    env:'t env ->
    NunUntypedAST.statement ->
    ('t statement * 't env) or_error

  val convert_statement_exn :
    env:'t env ->
    NunUntypedAST.statement ->
    't statement * 't env
  (** Unsafe version of {!convert} *)

  type 't problem = ('t, 't, stmt_invariant) NunProblem.t

  val convert_problem :
    env:'t env ->
    NunUntypedAST.statement list ->
    ('t problem * 't env) or_error

  val convert_problem_exn :
    env:'t env ->
    NunUntypedAST.statement list ->
    't problem * 't env
end

(** Decoding function used by {!pipe} *)
val erase :
  repr:('t, _) NunTerm_ho.repr ->
  't NunModel.t ->
  NunUntypedAST.term NunModel.t

(** Pipeline component. Takes input and output Term representations. *)
val pipe :
  print:bool ->
  build1:'t1 NunTerm_typed.build ->
  build2:('t2, NunTerm_typed.invariant) NunTerm_ho.build ->
  (NunUntypedAST.statement list,
    ('t1, 't1, stmt_invariant) NunProblem.t,
    't2 NunModel.t, NunUntypedAST.term NunModel.t)
    NunTransform.t

val pipe_with :
  decode:(signature:'a NunSignature.t -> 'c -> 'd) ->
  print:bool ->
  build:'t NunTerm_typed.build ->
  (NunUntypedAST.statement list,
    ('t, 't, stmt_invariant) NunProblem.t, 'c, 'd
  ) NunTransform.t
