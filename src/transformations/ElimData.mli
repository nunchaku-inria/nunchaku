
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Datatypes}

     encode (co)datatypes.
     a [data a =  c1 x1 | ... | cn xn] becomes a type [a]
     plus axioms defining each constructor, selector and tester. *)

open Nunchaku

type term = TermInner.Default.t

type mode =
  | M_data
  | M_codata

val pp_mode : mode CCFormat.printer

module type S = sig
  type decode_state

  val mode : mode

  val name : string

  val transform_pb :
    (term, term) Problem.t ->
    (term, term) Problem.t * decode_state

  val decode_model :
    decode_state -> (term, term) Model.t -> (term, term) Model.t

  val pipe :
    print:bool ->
    check:bool ->
    ((term,term) Problem.t,
     (term,term) Problem.t,
     (term,term) Problem.Res.t, (term,term) Problem.Res.t
    ) Transform.t

  val pipe_with :
    ?on_decoded:('d -> unit) list ->
    decode:(decode_state -> 'c -> 'd) ->
    print:bool ->
    check:bool ->
    ((term,term) Problem.t,
     (term,term) Problem.t, 'c, 'd
    ) Transform.t
end

module Data : S
module Codata : S
