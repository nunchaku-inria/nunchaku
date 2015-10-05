
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

module ConvertTerm(Term : TERM) : sig
  type env

  val empty_env : env

  module ConvertTy : sig
    val convert : env:env -> NunUntypedAST.ty -> Term.Ty.t or_error
    (** [convert ~env ty] converts the raw, unscoped type [ty] into a
        type from the representation [Ty.t].
        It returns an error if the type is ill-scoped. *)

    val convert_exn : env:env -> NunUntypedAST.ty -> Term.Ty.t
    (** @raise ScopingError if the type isn't well-scoped *)
  end

  type attempt_stack = NunUntypedAST.term list
  (** a trace of inference attempts with a message and optional location
      for each attempt. *)

  exception TypeError of string * attempt_stack
  (** Raised when the input is ill-typed or could not be inferred. *)

  val convert : env:env -> NunUntypedAST.term -> Term.t or_error
  (** [convert ~env ty] converts the raw, unscoped type [ty] into a
      type from the representation [Ty.t].
      It returns an error if the type is ill-scoped. *)

  val convert_exn : env:env -> NunUntypedAST.term -> Term.t
  (** Unsafe version of {!convert}
      @raise TypeError if it fails to  type properly *)

  val generalize : Term.t -> Term.t * Term.Ty.t var list
  (** Generalize a term [t] by parametrizing it over its free {b type}
      variables.
      @return a pair [(t', vars)] such that, roughly, [app t' vars = t] *)
end

(** {2 Statements} *)

module ConvertStatement(T : TERM) : sig
  module CT : module type of ConvertTerm(T)

  type t = (T.t, T.Ty.t) NunStatement.t

  type env = CT.env

  val empty_env : env

  val convert : env:env -> NunUntypedAST.statement -> (t * env) or_error

  val convert_exn : env:env -> NunUntypedAST.statement -> t * env
  (** Unsafe version of {!convert} *)

  val convert_list : env:env -> NunUntypedAST.statement list -> (t list * env) or_error

  val convert_list_exn : env:env -> NunUntypedAST.statement list -> t list * env
end

