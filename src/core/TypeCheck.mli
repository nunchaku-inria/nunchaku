
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Type Checking of a problem}

    This is used to check some invariants, in particular well-typedness,
    on internal AST *)

exception Error of string

module Make(T : TermInner.S) : sig
  type t

  val empty :
    ?check_non_empty_tys:bool ->
    ?env:(T.t, T.t) Env.t ->
    unit ->
    t

  val check_statement : t -> (T.t, T.t) Statement.t -> t
  (** [check_statement t st] checks that [st] is well typed and well-formed,
      and then return a new [t] that can be used to check subsequent statements *)

  val check_problem :
    t ->
    (T.t, T.t) Problem.t ->
    unit
    (** Check invariants on all the problem's statements
        @param check_non_empty_tys if true, also check that no statement
         defines an empty type. default false. *)
end
