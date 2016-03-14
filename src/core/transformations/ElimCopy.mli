
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate Copy Types} *)

type ('a,'b) inv = <eqn:'a; ind_preds:'b; ty:[`Mono]>

val name : string

module Make(T : TermInner.S) : sig
  type term = T.t

  val elim :
    (term, term, ('a, 'b) inv) Problem.t ->
    (term, term, ('a, 'b) inv) Problem.t

  val pipe :
    print:bool ->
    check:bool ->
    ((term, term, ('a, 'b) inv) Problem.t,
     (term, term, ('a, 'b) inv) Problem.t,
     'c, 'c) Transform.t
end
