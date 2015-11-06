
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

type id = NunID.t

(* TODO miniscoping *)

module type S = sig
  module T1 : NunTerm_ho.REPR
  module T2 : NunTerm_ho.BUILD

  type 'i state

  val create : ?prefix:string -> unit -> 'i state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : 'inv T1.t -> 'inv T2.t
  (** Put term in negation normal form *)

  val skolemize : state:'i state -> 'i T2.t -> 'i T2.t * (id * 'i T2.t) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> _ state -> unit

  val convert_problem :
    state:'i state ->
    ('i T1.t, 'i T1.t, 'inv) NunProblem.t ->
    ('i T2.t, 'i T2.t, 'inv) NunProblem.t

  val find_id_def : state:'i state -> id -> 'i T2.t option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:'i state -> 'i T2.t NunModel.t -> 'i T2.t NunModel.t

  val pipe :
    print:bool ->
    (('inv T1.t,'inv T1.t,'inv_p) NunProblem.t,
      ('inv T2.t,'inv T2.t,'inv_p) NunProblem.t,
      'inv T2.t NunModel.t, 'inv T2.t NunModel.t
    ) NunTransform.t

  (** Similar to {!pipe} but with a generic decode function.
      @param decode is given [find_id_def], which maps Skolemized
        constants to the formula they define *)
  val pipe_with :
    decode:(find_id_def:(id -> 'inv T2.t option) -> 'c -> 'd) ->
    print:bool ->
    (('inv T1.t,'inv T1.t,'inv_p) NunProblem.t,
      ('inv T2.t,'inv T2.t,'inv_p) NunProblem.t, 'c, 'd
    ) NunTransform.t
end

module Make(T1 : NunTerm_ho.REPR)(T2 : NunTerm_ho.BUILD)
  : S with module T1 = T1 and module T2 = T2
