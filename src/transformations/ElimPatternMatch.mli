
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate pattern-matching in Terms}

  Eliminate terms
  [match t with A x -> a | B -> b | C y z -> c]
  into
  [if is-A t then a[x := select-A-0 t]
   else if is-B t then b
   else c[y := select-C-0 t, z := select-C-1 t]
  ]

  which is a decision tree understandable by CVC4
*)

open Nunchaku

type term = TermInner.Default.t

val name : string

val elim_match : term -> term

val tr_problem:
  (term, term) Problem.t ->
  (term, term) Problem.t

val pipe :
  print:bool ->
  check:bool ->
    ((term, term) Problem.t,
     (term, term) Problem.t,
    'c, 'c
  ) Transform.t
(** Pipeline component. Reverse direction is identity. *)
