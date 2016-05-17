
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Encoding of Recursive Functions}

    Useful for finite-model finding in CVC4.
    It encodes recursive functions as axioms, with a quantification over
    an uninterpreted abstraction type. *)

open Nunchaku_core

module T = TermInner.Default

type inv1 = <ty:[`Mono]; eqn:[`App]; ind_preds:[`Absent]>
type inv2 = <ty:[`Mono]; eqn:[`Absent]; ind_preds:[`Absent]>

val name : string

exception Attr_is_handle_cstor
(** [Attr_is_handle_cstor] means that the ID is the binary type symbol
    that represents arrows for partially applied functions *)

exception Attr_app_val
(** [Attr_app_val] means that the ID being defined is an "application function"
    that is used to encode HO partial application into regular FO total
    application. There is only one application symbol per type. *)

exception Attr_proto_val of ID.t * int
(** [Attr_proto_val (f,k)] means the ID currently being declared is the [k]-th "proto"
    function used for default values. This "proto" is paired to the symbol [f],
    which is an application symbol of type [handle -> a_1 -> ... -> a_n -> ret],
    where the proto has type [handle -> a_k]. *)

type term = T.t
type decode_state

val elim_recursion :
  (term, term, inv1) Problem.t ->
  (term, term, inv2) Problem.t * decode_state

val decode_model :
  state:decode_state ->
  (term, term) Model.t ->
  (term, term) Model.t

(** Pipeline component *)
val pipe :
  print:bool ->
  check:bool ->
  ((term, term, inv1) Problem.t,
    (term, term, inv2) Problem.t,
    (term, term) Problem.Res.t,
    (term, term) Problem.Res.t) Transform.t

(** Generic Pipe Component
    @param decode the decode function that takes an applied [(module S)]
      in addition to the state *)
val pipe_with :
  ?on_decoded:('d -> unit) list ->
  decode:(decode_state -> 'c -> 'd) ->
  print:bool ->
  check:bool ->
  ((term, term, inv1) Problem.t,
    (term, term, inv2) Problem.t,
    'c, 'd
  ) Transform.t

