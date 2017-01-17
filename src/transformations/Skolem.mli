
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

open Nunchaku_core

type ty = TermInner.Default.t
type term = TermInner.Default.t

val name : string

type mode =
  [ `Sk_types (** Skolemize type variables only *)
  | `Sk_ho (** Skolemize type variables and term variables of fun type *)
  | `Sk_all (** All variables are susceptible of being skolemized *)
  ]

type state

module type SKOLEM = sig
  type state
  type assoc

  val create: ?prefix:string -> unit -> state

  val skolemize :
    state ->
    vars:ty Var.t list ->
    ty_ret:ty ->
    (ty -> assoc) ->
    ID.t * ty * assoc
  (** [skolemize state ~vars ~ty_ret assoc] makes a fresh ID that
      has the type [ty = List.map Var.ty vars -> ty_ret].
      It registers it in [state] so that it will be returned on
      the next call to {!pop_new_decls}, and it will map
      it to [assoc ty]
      @return the new ID and its type *)

  val pop_new_decls : state -> (ID.t * assoc) list
  (** Remove new declarations from [state] and return them *)

  val find_skolem : state -> ID.t -> assoc option
  (** If the given ID a skolem symbol, return associated data *)

  val all_skolems : state -> (ID.t * assoc) Sequence.t
end

module Make(Assoc : sig type t end) : SKOLEM with type assoc = Assoc.t

val create : ?prefix:string -> mode:mode -> unit -> state
(** @param prefix the prefix used to generate Skolem symbols
    @param mode the kind of skolemization we expect *)

val skolemize :
  state:state ->
  ?in_goal:bool ->
  Polarity.t ->
  term ->
  term * (ID.t * term) list
(** [skolemize ~state pol t] returns [t', new_syms] where [t'] is
    the skolemization of [t] under polarity [pol],
    and [new_syms] is a set of new symbols with their type
    @param in_goal if true, record skolem definitions so that they can
      appear in the model *)

val print_state : Format.formatter -> state -> unit

val skolemize_pb :
  state:state ->
  (term, term) Problem.t ->
  (term, term) Problem.t

val decode_model :
  skolems_in_model:bool ->
  state:state ->
  (term,term) Model.t -> (term,term) Model.t
(** Decode the given model
    @param skolems_in_model if true, skolem constants will stay in the
      model after decoding; otherwise they are dropped *)

val pipe :
  skolems_in_model:bool ->
  mode:mode ->
  print:bool ->
  check:bool ->
  ((term,term as 'inv) Problem.t,
   (term,term) Problem.t,
   (term,term) Problem.Res.t, (term,term) Problem.Res.t
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
  ((term,term) Problem.t,
   (term,term) Problem.t, 'c, 'd
  ) Transform.t
