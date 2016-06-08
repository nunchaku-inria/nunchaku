
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Type Checking of a problem}

    This is used to check some invariants, in particular well-typedness,
    on internal AST *)

exception Error of string

module Make(T : TermInner.S) : sig
  type env

  val empty_env : unit -> env

  val check_statement : env -> (T.t, T.t) Statement.t -> env
  (** [check_statement env st] checks that [st] is well typed and well-formed,
      and then return a new [env] that can be used to check subsequent statements *)

  val check_problem : ?env:env -> (T.t, T.t) Problem.t -> unit
  (** Check invariants on all the problem's statements *)
end


