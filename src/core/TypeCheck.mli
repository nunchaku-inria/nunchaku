
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Type Checking of a problem}

    This is used to check some invariants, in particular well-typedness,
    on internal AST *)

exception Error of string

module Make(T : TermInner.S) : sig
  type 'inv env

  val empty_env : unit -> 'inv env

  val check_statement : 'inv env -> (T.t, T.t, 'inv) Statement.t -> 'inv env
  (** [check_statement env st] checks that [st] is well typed and well-formed,
      and then return a new [env] that can be used to check subsequent statements *)

  val check_problem : ?env:'inv env -> (T.t, T.t, 'inv) Problem.t -> unit
  (** Check invariants on all the problem's statements *)
end


