
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Transform a problem with multiple equations per defined Symbol into one with single equations} *)

type id = ID.t

type 'a inv1 = <ty:'a; eqn:[`Nested]>
type 'a inv2 = <ty:'a; eqn:[`Single]>

module Make(T : TermInner.S) : sig
  type term = T.t

  exception Error of string

  val uniq_eqns_pb :
    (term, term, 'a inv1) Problem.t ->
    (term, term, 'a inv2) Problem.t

  (** Pipeline component *)
  val pipe :
    decode:('b -> 'c) ->
    print:bool ->
    ((term, term, 'a inv1) Problem.t,
      (term, term, 'a inv2) Problem.t,
      'b, 'c) Transform.t
end



