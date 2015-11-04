
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Skolemization} *)

type id = NunID.t

(* TODO miniscoping *)

module type S = sig
  module T1 : NunTerm_ho.VIEW
  module T2 : NunTerm_ho.S
    with type invariant_poly = T1.invariant_poly
    and type invariant_meta = T1.invariant_meta

  type state

  val create : ?prefix:string -> unit -> state
  (** @param prefix the prefix used to generate Skolem symbols *)

  val nnf : T1.t -> T2.t
  (** Put term in negation normal form *)

  val skolemize : state:state -> T2.t -> T2.t * (id * T2.ty) list
  (** [skolemize ~state t] returns [t', new_syms] where [t'] is
      the skolemization of [t], and [new_syms] is a set of new symbols
      with their type *)

  val print_state : Format.formatter -> state -> unit

  val convert_problem :
    state:state ->
    (T1.t, T1.ty, 'inv) NunProblem.t ->
    (T2.t, T2.ty, 'inv) NunProblem.t

  val find_id_def : state:state -> id -> T2.t option
  (** Find definition of this Skolemized ID *)

  val decode_model :
    state:state -> T2.t NunModel.t -> T2.t NunModel.t
end

module Make(T1 : NunTerm_ho.VIEW)(T2 :
  NunTerm_ho.S
  with type invariant_poly = T1.invariant_poly
  and type invariant_meta = T1.invariant_meta
) : S with module T1 = T1 and module T2 = T2

val pipe :
  print:bool ->
  (module NunTerm_ho.VIEW with type t = 'a) ->
  (module NunTerm_ho.S with type t = 'b) ->
  (('a,'a,'inv) NunProblem.t, ('b,'b,'inv) NunProblem.t,
    'b NunModel.t, 'b NunModel.t
  ) NunTransform.t

(** Similar to {!pipe} but with a generic decode function.
    @param decode is given [find_id_def], which maps Skolemized
      constants to the formula they define *)
val pipe_with :
  decode:(find_id_def:(id -> 'b option) -> 'c -> 'd) ->
  print:bool ->
  (module NunTerm_ho.VIEW with type t = 'a) ->
  (module NunTerm_ho.S with type t = 'b) ->
  (('a,'a,'inv) NunProblem.t, ('b,'b,'inv) NunProblem.t, 'c, 'd) NunTransform.t

