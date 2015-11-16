
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Eliminate pattern-matching in Equations and Terms}

  Transform an equation
  [forall x y. f (x :: y) = rhs]
  into
  [forall l. is_cons l => f l = rhs(x:=select_cons_1 l, y:=select_cons_2 l)]

  Namely, it changes an equations with a pattern on the left, into an equation
  with a linear irrefutable pattern on the left; in other words, the result
  has the form
  [forall x1...xn, f x1...xn = rhs]

  Another example:
  [f (s 0) = rhs]
  becomes
  [forall l. is_s l && is_0 (select_s_1 l) ==> f l = rhs]

  Also change pattern matching in terms into a (naive) discrimination tree:
  [match t with A x -> a | B -> b | C y z -> c]
  becomes
  [if is-A t then a[x := select-A-0 t]
   else if is-B t then b
   else c[y := select-C-0 t, z := select-C-1 t]
  ]

  A non-algebraic type could be encoded using an existential:

  [forall x. f (g x) = rhs]
  might become
  [forall y. (exists x. y = g x => f y = rhs[x := ??]

  but we lack some choice operator.
*)

type id = NunID.t

exception Error of string

module Make(T : NunTermInner.S) : sig
  type term = T.t
  type env = (term, term, <ty:[`Mono]; eqn:[`Linear]>) NunEnv.t

  val tr_statement :
    env:env ->
    (term, term, <ty:[`Mono]; eqn:[`Nested]>) NunStatement.t ->
    env * (term, term, <ty:[`Mono]; eqn:[`Linear]>) NunStatement.t
  (** Flatten a single equation, using inductive selectors/discriminators
      and existential variables for eliminating the left-hand side pattern.
      Preserves other statements identically.
      @param env the current environment
      @raise Error if the equation LHS is not a proper pattern *)

  val tr_problem:
    (term, term, <ty:[`Mono]; eqn:[`Nested]>) NunProblem.t ->
    (term, term, <ty:[`Mono]; eqn:[`Linear]>) NunProblem.t

  val pipe :
    print:bool ->
      ((term, term, <ty:[`Mono]; eqn:[`Nested]>) NunProblem.t,
       (term, term, <ty:[`Mono]; eqn:[`Linear]>) NunProblem.t,
      'b, 'b
    ) NunTransform.t
  (** Pipeline component. Reverse direction is identity. *)
end
