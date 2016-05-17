
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

open Nunchaku_core

module T = TermInner.Default

val name : string

type mode =
  [ `Sk_types (** Skolemize type variables only *)
  | `Sk_ho (** Skolemize type variables and term variables of fun type *)
  | `Sk_all (** All variables are susceptible of being skolemized *)
  ]

type state

val create : ?prefix:string -> mode:mode -> unit -> state
(** @param prefix the prefix used to generate Skolem symbols
    @param mode the kind of skolemization we expect *)

val skolemize : state:state -> Polarity.t -> T.t -> T.t * (ID.t * T.t) list
(** [skolemize ~state pol t] returns [t', new_syms] where [t'] is
    the skolemization of [t] under polarity [pol],
    and [new_syms] is a set of new symbols with their type *)

val print_state : Format.formatter -> state -> unit

val skolemize_pb :
  state:state ->
  (T.t, T.t, <eqn:_;ind_preds:_;ty:_;..> as 'inv) Problem.t ->
  (T.t, T.t, 'inv) Problem.t

val find_id_def : state:state -> ID.t -> T.t option
(** Find definition of this Skolemized ID *)

val decode_model :
  state:state -> (T.t,T.t) Model.t -> (T.t,T.t) Model.t

val pipe :
  mode:mode ->
  print:bool ->
  check:bool ->
  ((T.t,T.t,<eqn:_;ind_preds:_;ty:_;..> as 'inv) Problem.t,
    (T.t,T.t,'inv) Problem.t,
    (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
  ) Transform.t

(** Similar to {!pipe} but with a generic decode function.
    @param mode determines which variables are skolemized
    @param print if true, prints problem after skolemization
    @param check if true, check the invariants on the result
    @param decode is given [find_id_def], which maps Skolemized
      constants to the formula they define *)
val pipe_with :
  mode:mode ->
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((T.t,T.t, <eqn:_;ind_preds:_;ty:_;..> as 'inv) Problem.t,
    (T.t,T.t,'inv) Problem.t, 'c, 'd
  ) Transform.t
