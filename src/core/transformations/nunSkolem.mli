
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

type id = NunID.t

(* TODO miniscoping *)

module type PARAM = sig
  type term1
  type term2

  val repr1: (term1, 'inv) NunTerm_ho.repr
  val build2: (term2, 'inv) NunTerm_ho.build
end

module type S = sig
  include PARAM

  type state

  val create : ?prefix:string -> unit -> state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : term1 -> term2
  (** Put term in negation normal form *)

  val skolemize : state:state -> term2 -> term2 * (id * term2) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> state -> unit

  val convert_problem :
    state:state ->
    (term1, term1, 'inv) NunProblem.t ->
    (term2, term2, 'inv) NunProblem.t

  val find_id_def : state:state -> id -> term2 option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:state -> term2 NunModel.t -> term2 NunModel.t
end

module Make(P : PARAM)
  : S with type term1 = P.term1 and type term2 = P.term2

val pipe :
  print:bool ->
  repr1:('t1,'inv) NunTerm_ho.repr ->
  build2:('t2,'inv) NunTerm_ho.build ->
  (('t1,'t1,'inv) NunProblem.t,
    ('t2,'t2,'inv) NunProblem.t,
    't2 NunModel.t, 't2 NunModel.t
  ) NunTransform.t

(** Similar to {!pipe} but with a generic decode function.
    @param decode is given [find_id_def], which maps Skolemized
      constants to the formula they define *)
val pipe_with :
  decode:(find_id_def:(id -> 't2 option) -> 'c -> 'd) ->
  print:bool ->
  repr1:('t1,'inv) NunTerm_ho.repr ->
  build2:('t2,'inv) NunTerm_ho.build ->
  (('t1,'t1,'inv) NunProblem.t, ('t2,'t2,'inv) NunProblem.t, 'c, 'd) NunTransform.t

