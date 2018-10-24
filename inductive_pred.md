# Inductive Predicates

keyword: `pred/copred`

    copred a : foo -> prop :=
      a x & b (f x) => a (s x);
      a 0
    and b : bar -> prop := ....

Each rhs should start with the defined predicate and contain no other occurrence of the predicates being defined.

Flag `well-founded` (or variant `wf-pred` / `wf-copred`) as an option/attribute. For well-founded predicates, encoding straightforward (turn into a `rec` definition, then encoding of rec functions).

not well-founded: add an argument (of type `nat`) that decreases at each call:

    pred even n :=
      even 0;
      even n => even n;
      even n => even (s (s n)).

    # use even
    p (even n0).

becomes, with an approximation of depth `k`:

    wf-pred even k n :=
      even 0 _ = false;  # we start at 1
      even (s k) 0;
      even k n => even (s k) n;
      even k n => even (s k) (s (s n)).

    val k0: nat.

    # use even:
    p (even k0 n0).

and then we can reverse the definition and turn it into a recursive function.

| definition | + | - | ± |
| --- | --- | --- | --- |
| wf-pred     | rec     | rec       | rec
| pred        | unroll  | rec       | guard
| copred      | rec     | co-unroll | guard

where:

-   unroll means using the additional `k` argument, then same as `rec`
-   co-unroll is the same as `unroll` but the 0 case is `true`, not `false`
-   rec means the usual encoding of recursive functions
-   guard means duplicating `p` into a positive version `p⁺` and a negative version `p⁻`, defined with rec and (co)-unroll respectively (see above), and everywhere `p t1...tn` is used we use, say, `p⁺ t1...tn` with a guard `p⁺ t1...tn = p⁻ t1...tn`.


