
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate "if/then/else"}

     Example:
     [if a&b then case else if c&d then case2 else case3]
     becomes
     [(a&b) => case1;
      (not (a&b) & c&d) => case2;
      (not(a&b) & not (c&d)) => case3
     ]
*)

open Nunchaku_core

type term = FO.T.t
type ty = FO.Ty.t
type problem = (term, ty) FO.Problem.t

val name : string

val transform_term : term -> term
(** transform a propositional term into a conjunction of [condition => term], where
    each condition is orthogonal to the previous ones *)

val transform_statement : (term, ty) FO.statement -> (term, ty) FO.statement

val transform_problem : problem -> problem

val pipe :
  print:bool ->
  (problem, problem, 'a, 'a) Transform.t
