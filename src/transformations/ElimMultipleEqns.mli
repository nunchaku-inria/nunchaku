
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

open Nunchaku_core

type id = ID.t

type ('a,'b) inv1 = <ty:'a; ind_preds:'b; eqn:[`Nested]>
type ('a,'b) inv2 = <ty:'a; ind_preds:'b; eqn:[`Single]>

val name : string

module Make(T : TermInner.S) : sig
  type term = T.t

  exception Error of string

  val uniq_eqns_pb :
    (term, term, ('a,'b) inv1) Problem.t ->
    (term, term, ('a,'b) inv2) Problem.t

  (** Pipeline component *)
  val pipe :
    decode:('c -> 'd) ->
    print:bool ->
    check:bool ->
    ((term, term, ('a,'b) inv1) Problem.t,
      (term, term, ('a,'b) inv2) Problem.t,
      'c, 'd) Transform.t
end



