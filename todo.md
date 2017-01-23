# TODO

## Now

## Main

- add `def f (x:a) (y:b): c := <rhs>` to the parser
  and possibly to printer (after `elim_multi_eqns`), for easier
  human input

- [ ] make a proper SMBC pipeline
  * [x] in smbc, need to support projectors/destructors
  * [x] removal of bad quantifiers/equality
  * [x] remove `intro-guards`, use SMBC's builtin `asserting`
  * [x] transform unknowns into new toplevel constants (maybe at the last moment)
  * [ ] better model parsing?

  `./nunchaku.native -s smbc --print-all -t 30 problems/tests/choice_sym.nun`

- [ ] in main pipeline, make `Error` non-shortcut (if one backend fails,
      e.g. smbc because of a stack overflow, ignore it/ emit warning)?

- [ ] inlining transformation (quite aggressive) on non-recursive definitions

- [ ] add `[wf]` to `rec`, useful for Coq frontend and for some Isabelle definitions.
      **OR** make `wf` the default and have some attribute for other cases

- [ ] flag to print signature (post-type inference)

- [ ] deal with empty sorts (in CVC4)

- [ ] add dependent type (+ encoding step before mono)

#### Refactoring

- [ ] merge `Env` and `Traversal.Partial_statement`
- [ ] refactor Stmt to use `defined` more; also rename "tydef" into "data"

#### TPTP

- [ ] print models in TPTP syntax
- [ ] detect some WF definitions and use `rec`
- add `let` in THF parser

#### Delayed

some tasks that might not be useful in the end

- ~~[ ] module to compute if a symbol is deterministic (similar to `AnalyzeType`).
      It is if it uses (recursively) any of `unknown,spec,val`~~

## Doc

- [ ] https://nunchaku-inria.github.io/nunchaku/
  Put the readme in there, with a few examples!!
  * each example should be a code block for input illustrating some features,
    the command to invoke nunchaku and the output

## Long-Term

- [ ] dependent types for better encodings from Coq/Lean

- [ ] logo?

## Done

- [x] in specialize
  * [x] add self-congruence axioms
  * [x] eliminate arguments that have "bad" closure variables in them,
       but still allow to specialize w.r.t the other arguments
- [x] remove `assuming`
- [x] use `Env` instead of signatures for type inference
- [x] define `choice p` using `unknown (choice p) asserting …`
- [x] add `default` case to the `match` construct (should allow for better
    encodings of some pattern-matches)
  * also add it to main syntax?
  * [x] use the one from TIP
- [x] compute type cardinalities to approximate exists/forall with top/bot in non polarized cases
- [x] scoping and type inference from AST
- [x] basic printing to CVC4
- [x] distinct cases Var/Meta (one unifies, the other doesn't) due:2015-10-05
- [x] conversion term_typed -> term_ho
- [x] add a notion of goal?
- [x] basic parsing of CVC4
- [x] conversion ho -> fo
- [x] parser/problem: axiomes [def,spec], avec plusieurs cas (équations rec); merger def/def_prop, decl/ty_decl
- [x] fix conflicts in parser
- [x] basic monomorphization term_ho -> term_fo
- [x] pipeline parsing -> scoping/type infer -> cvc4
- [x] interdire re-definition de symboles
- [x] refactor AST (make Eq,Ite builtins; factor binders together)
- [x] fix/check typing in syntax.nun
- [x] extend monomorphization to (co)data
- [x] sanity checks on (co)inductive types at type inference
- [x] send (co)data to CVC4
- [x] search for included files in same dir as problem
- [x] restrictions on typing: prenex polymorphism
- [x] parse THF fragment
- [x] parser TPTP
- [x] add ite in THF
- [x] use vector instead of list for statements?
- [x] make `pipe` operators that take `decode` as arg
- [x] un-nesting/mutualization of (co)data
- [x] fix skolemization
- [x] recursive definitions (with well-foundedness check)
- [x] fix mangling
- [x] split unrolling off polarize?
- [x] fix polarization (use same var in whole block, with table)
- [x] continue refactor
- [x] continue elim of recursion (by removing nested eqns first)
- [x] fix tests back
- [x] improve printing (especially _in_app stuff)
- [x] remove useless translation after type inference
- [x] accept non-atomic terms in RHS of definitions (no ambiguity)
- [x] allow declaration+definition in one statement
- [x] fix bug in elim_multi_eqns due:2015-12-02
- [x] try several CLI flags for CVC4 (see mail)
- [x] include statement due:2015-12-08
- [x] run several instances of CVC4 in parallel (portfolio)
- [x] find a clean way to do scheduling
- [x] parametrize builtins by their arguments?
- [x] add builtins for polarized functions
- [x] syntax for (co)ind predicates
- [x] put polarization in ID, remove it from builtin
- [x] after monomorphization, IDs do not need `@` anymore
- [x] polarization of (co)ind predicates
- [x] translation of (co)ind predicates to recursive functions
- [x] inductive propositions due:2015-12-10
- [x] print models like problems
- [x] fix issues in model translation (see doc/)
- [x] do not unroll/encode inductive preds with 0 args
- [x] decoding of polarized symbols
- [x] add type aliases (with conversion functions) @feature
- [x] split skolemization into 1/ early skolemization of types  2/ late sk. of terms (maybe only HO vars)
- [x] a constant rec is a spec
- [x] allow ambiguous matching, resolved by order (ML-like)
- [x] harmonize names in debug/print CLI options @cleanup
- [x] use bisect for test coverage http://bisect.x9c.fr/distrib/bisect.html#htoc10 @test
- [x] release
- [x] printTPTP: need types (differentiate type args from term args; 1 domain decl per type)
- [x] print models in TPTP properly @feature
- [x] finish specialization (emit extensionality axioms) @feature
- [x] make specialize handle ind. preds.
- [x] optional type-checking fence after each step
- [x] fix bug in ElimHOF (need to declare more, earlier for ty_exn to work) --> polarity2
- [x] µ terms, parse them from CVC4 and deal with them internally
- [x] system of dependencies for passes (checked at pipeline-build time); replace old GADT
- [x] pass to eliminate predicate arguments (using pseudo-prop type + ite)
- [x] system of dependencies for passes (checked at pipeline-build time); replace old GADT
- [x] printer: have binding power argument to put ( ) properly @cleanup
- [x] fix model parsing for paradox (see spec_inval_def2.nun)
- [x] improve Elim_prop_args (type-driven recursive traversal)
- [x] refine ElimRec to avoid boxing small products of finite types (useful for paradox)
- [x] ElimData: use asserting for defining cons/nil (see mockup)
- [x] narrowing @feature
- [x] copy tip-parser in src/parsers/
- [x] --dump option for dumping sub-problems to files
