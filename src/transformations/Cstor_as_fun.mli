
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Introduce Functions for Partially Applied Constructors} *)

open Nunchaku_core

type ty = Term.t
type term = Term.t
type var = ty Var.t
type env = (term,term) Env.t

val name : string
val long_name : string

type state = {
  cstor_funs_map: ID.t ID.Tbl.t;
  (* constructors-as-functions, for partial applications *)
  cstor_funs_set: unit ID.Tbl.t;
  (* set of constructors-as-functions introduced so far*)
}

val create : unit -> state

val is_defined_fun : state -> ID.t -> bool
(** Is this a function standing for a constructor? *)

type def = ty Statement.defined * var list * term
(** The definition of a term *)

val cstor_as_fun : state -> ID.t -> ty:term -> ID.t * def option
(** [cstor_as_fun state env c] assumes [c] is defined as a constructor
    in [env], and retrieve the corresponding function if it exists.
    Otherwise it defines a new one, paired with its definition *)

val encode_pb : (term,term) Problem.t -> (term,term) Problem.t * state

val decode_model : state -> (term, term) Model.t -> (term, term) Model.t

(** Pipeline component *)
val pipe :
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   (term, term) Problem.Res.t,
   (term, term) Problem.Res.t) Transform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  ?on_decoded:(('d -> unit) list) ->
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term) Problem.t,
   (term, term) Problem.t,
   'c, 'd
  ) Transform.t
