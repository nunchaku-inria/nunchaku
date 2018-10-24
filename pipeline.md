# Pipeline components

- type inference:
  infer implicit type parameters, and check that the problem is well-typed

- skolemization:
  replace existential variables in the goal by fresh constant/function symbols

- monomorphization:
  specialize polymorphic functions and types, and perform dependency analysis to keep only the relevant types and definitions

- elim matching:
  encode pattern matching into `DataSelect` / `DataTest` constructs that can be used by CVC4

- recursion elimination:
  [encoding](#rec_elim_encoding) of recursive functions that are more suitable for CVC4’s finite model finding.

- conversion to FO:
  check that the problem is now monomorphic first-order, and translate it to a specialized format

- elim multiple equations:
  (**wip**) convert Haskell-like definitions, with multiple definitions for a single function, into a single-equation + pattern matching (à la Coq).

- specialization:
  (**todo**) specialize higher-order functions (e.g., `map` or `fold`) to their functional arguments, to obtain a first-order function. For instance, `map (fun x -> x+1)` should become `map_42 : list nat -> list nat` where `map_42 l = match l with nil -> nil | cons x l -> cons (x+1) (map_42 l) end`

- inlining/unfolding:
  (**todo**) related to specialization, this replaces some non-recursive functions by their definition

- encoding HO functions to arrays:
  (**todo**) to have CVC4 synthesize some function `τ1 → τ2` passed as argument to another function, where `τ1` is a finite type, encode the function as an `array τ1 τ2`.

- encoding dependent types:
  (**todo**) once we have dependent types, remove term arguments to a type and instead use some predicate to enforce typing invariant. For instance, `vec : nat -> type -> type` becomes `vec_ : type -> type`, and `forall v:(vec n τ). p[v]` becomes `forall v:(vec τ). well-formed-vec n v => p[v]` where `well-formed-vec n v` is an inductive predicate basically enforcing that `n = length v`.

- Backends:

  * CVC4:
    send the first-order problem to CVC4 in SMTlib syntax, and read a model back if it indicates `SAT`.

  * Narrowing (smbc):
    (**wip**) given a problem where every symbol is computable (defined as a function rather than uninterpreted symbol + axioms), use symbolic evaluation + refinement of variables of inductive type to obtain counter-example values.

## Recursive Functions

The recursive (well-founded) functions need to be encoded:

    val fib : nat -> nat

    let rec fib n =
      if n = 0 then 0
      else if n = 1 then 1
      else
        fib (n-1) + fib (n-2)

requires quantification over `nat : type` which is infinite. Instead we approximate its argument by `gamma_nat : pseudo_nat -> nat` (uninterpreted type to be dealt with by finite model finding) and it becomes:

    val fib : nat -> nat

    forall x. gamma_nat x = 0 => fib (gamma_nat x) = 0.
    forall x. gamma_nat x = 1 => fib (gamma_nat x) = 1.
    forall x.
      exists m1 m2.
          gamma_nat m1 = (gamma_nat n) - 1 && gamma_nat m2 = (gamma_nat n) - 2
          =>
          fib (gamma_nat n) = fib (gamma_nat m1) + fib (gamma_nat m2))

See *Model Finding for Recursive Functions in SMT*. Also, model extraction should only translate `fib` on a domain restricted to values that are in the image of `gamma_nat` (other values are "junk").

For (co)inductive types, selectors and tester should be used since SMT solvers do not have pattern-matching (yet?).

## Inductive Predicates

Syntax:

    inductive even : nat -> prop :=
      even 0 ;
      even n => even n ;  # not well-founded!
      even n => even (n+2).

Two possible approaches.

Reference <http://www.cl.cam.ac.uk/~jrh13/papers/ind.html>

### À la Coq

Add an argument that is used to make the recursion well-founded (or productive, for coinductive predicates).

    data even_witness :=
      | case0
      | case_same even_witness
      | case_plus2 even_witness.

    val even' : even_witness -> nat -> prop

    rec even' :=
      even' case0 0 ;
      even' (case_same w) n = even' w n ;
      even' (case_plus2 w) (n+2) = even' w n.

Note that every case is now well-founded.

### À la Nitpick

Approximation that depends on the polarity. Declare `even2 : nat -> nat -> prop` where the first `nat` is an index.

| positive | negative |
| --- | --- |
| `even2 0 _ = false` | `even2 0 _ = true` |
| `even2 k n = even2 (k-1) 0 ∨ even2 (k-1) n ∨ even2 (k-1) (n-2)` | same |

Then `even n` is either `exists k. even2 k n`, or we can enumerate `k` starting from `0` (or CVC4 could).
