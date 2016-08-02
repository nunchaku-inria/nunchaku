
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

val skolemize :
  state:state ->
  ?in_goal:bool ->
  Polarity.t ->
  T.t ->
  T.t * (ID.t * T.t) list
(** [skolemize ~state pol t] returns [t', new_syms] where [t'] is
    the skolemization of [t] under polarity [pol],
    and [new_syms] is a set of new symbols with their type
    @param in_goal if true, record skolem definitions so that they can
      appear in the model *)

val print_state : Format.formatter -> state -> unit

val skolemize_pb :
  state:state ->
  (T.t, T.t) Problem.t ->
  (T.t, T.t) Problem.t

val decode_model :
  skolems_in_model:bool ->
  state:state ->
  (T.t,T.t) Model.t -> (T.t,T.t) Model.t
(** Decode the given model
    @param skolems_in_model if true, skolem constants will stay in the
      model after decoding; otherwise they are dropped *)

val pipe :
  skolems_in_model:bool ->
  mode:mode ->
  print:bool ->
  check:bool ->
  ((T.t,T.t as 'inv) Problem.t,
    (T.t,T.t) Problem.t,
    (T.t,T.t) Problem.Res.t, (T.t,T.t) Problem.Res.t
  ) Transform.t

(** Similar to {!pipe} but with a generic decode function.
    @param mode determines which variables are skolemized
    @param print if true, prints problem after skolemization
    @param check if true, check the invariants on the result
    @param skolems_in_model if true, skolem constants will stay in the
      model after decoding; otherwise they are dropped
    @param decode is given [find_id_def], which maps Skolemized
      constants to the formula they define *)
val pipe_with :
  mode:mode ->
  decode:(state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((T.t,T.t) Problem.t,
    (T.t,T.t) Problem.t, 'c, 'd
  ) Transform.t
