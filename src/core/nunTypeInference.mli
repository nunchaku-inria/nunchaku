
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Scoping and Type Inference} *)

type 'a or_error = [`Ok of 'a | `Error of string]
type var = NunVar.t
type loc = NunLocation.t

exception ScopingError of string * string * loc option
(** Scoping error for the given variable *)

(** {2 Typed Term} *)
module type TERM = sig
  include NunTerm_intf.S_WITH_PRINTABLE_TY

  val loc : t -> loc option

  val ty : t -> Ty.t option
  (** Type of this term *)

  val builtin : ?loc:loc -> ty:Ty.t -> NunTerm_intf.Builtin.t -> t
  val var : ?loc:loc -> ty:Ty.t -> var -> t
  val app : ?loc:loc -> ty:Ty.t -> t -> t list -> t
  val fun_ : ?loc:loc -> ty:Ty.t -> var -> ty_arg:Ty.t -> t -> t
  val let_ : ?loc:loc -> var -> t -> t -> t
  val forall : ?loc:loc -> var -> ty_arg:Ty.t -> t -> t
  val exists : ?loc:loc -> var -> ty_arg:Ty.t -> t -> t

  val ty_type : Ty.t (** Type of types *)
  val ty_prop : Ty.t (** Propositions *)

  val ty_builtin : ?loc:loc -> NunType_intf.Builtin.t -> Ty.t
  val ty_var : ?loc:loc -> var -> Ty.t
  val ty_meta_var : ?loc:loc -> var -> Ty.t  (** Meta-variable, ready for unif *)
  val ty_app : ?loc:loc -> Ty.t -> Ty.t list -> Ty.t
  val ty_forall : ?loc:loc -> var -> Ty.t -> Ty.t
  val ty_arrow : ?loc:loc -> Ty.t -> Ty.t -> Ty.t
end

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

  val generalize : Term.t -> Term.t * var list
  (** Generalize a term [t] by parametrizing it over its free {b type}
      variables.
      @return a pair [(t', vars)] such that, roughly, [app t' vars = t] *)
end

(** {2 Statements} *)

module type STATEMENT = sig
  include NunStatement_intf.S

  module T : TERM

  val loc : (_,_) t -> loc option

  val decl : ?loc:loc -> var -> T.Ty.t -> (_, T.Ty.t) t
  val def : ?loc:loc -> var -> T.t -> (T.t, _) t
  val axiom : ?loc:loc -> T.t -> (T.t,_) t
end

module ConvertStatement(St : STATEMENT) : sig
  module CT : module type of ConvertTerm(St.T)

  type t = (St.T.t, St.T.Ty.t) St.t

  type env = CT.env

  val empty_env : env

  val convert : env:env -> NunUntypedAST.statement -> (t * env) or_error

  val convert_exn : env:env -> NunUntypedAST.statement -> t * env
  (** Unsafe version of {!convert} *)

  val convert_list : env:env -> NunUntypedAST.statement list -> (t list * env) or_error

  val convert_list_exn : env:env -> NunUntypedAST.statement list -> t list * env
end

