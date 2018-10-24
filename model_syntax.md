# Syntax of Generated Models

The syntax for models is, by default, the [native syntax](#native-syntax).
Alternative syntaxes can be picked with the `--output {nunchaku,tptp,sexp}` (or, for short, `-o`) command line option.

## Native Syntax (`-o nunchaku`)

A syntax that is nice on the eyes, and mostly mirrors the input format. For example, this is a model with one type and two constants:

    SAT: {
      type a := {$a_0, $a_1}.
      val xs := Cons $a_0 Nil.
      val ys := Cons $a_1 Nil.
    }

The output follows the following rules. `UNSAT`, `UNKNOWN`, or `ERROR` is printed if no model is found. If a model is found, it will look like:

    SAT: {
      <decl>*
    }

where each `<decl>` is either:

type declaration  
of the form `type <id> = {<dom_elt>*}.`, a finite type containing special constants called *domain elements* that are all distinct. Every term of this type is mapped, in the model, to one of these domain elements. Domain elements are identifiers starting with `$`.

value definition  
of the form `val term := term.`, defines the left-hand side term to be equal to the right-hand side term.

## S-expression based Syntax (`-o sexp`)

A simple S-expression based syntax for easy parsing by a tool. A model looks like this:

    (SAT
     ((type a ($a_0 $a_1))
      (val ys (Cons $a_1 Nil))
      (val xs (Cons $a_0 Nil))))

So it is isomorphic to the native syntax but uses S-expressions everywhere. The exact formatting of terms in S-expressions should look roughly like TIP but is not yet documented.

## TPTP syntax (`-o tptp`)

Loosely based on <http://www.cs.miami.edu/~tptp/TPTP/QuickGuide/FiniteInterpretations.html> but not thoroughly tested.

## Design Issues

### Syntax

The current output looks like an S-expression. For CVC4, such an output format makes a lot of sense, because SMT-LIB input is also a list of S-expressions (or something very similar). But for Nunchaku, this feels outlandish. Something like

    val elem := {@elem_1, @elem_2}.

for uninterpreted types and

    val append := fun ($xs : list). fun ($ys : list). blah_blah.

for terms would feel more natural (and wouldn’t be harded to parse). You could even go further and really use the input syntax, e.g.

    datatype elem = @elem_1 | @elem_2.
    rec append : list -> list -> list :=
      append $xs $ys = blah_blah.

(even if "elem" is an uninterpreted type, i.e., "val elem : type" in the input problem, and "append" is specified by something else than "rec"). The advantage of this scheme is that the output syntax is a subset of the input syntax. And one could in principle take the input file, replace the declaration of "elem" and the definition of "append" with the model output, rerun Nunchaku, and get SAT again (modulo little syntactic issues like "?\_\_", but even there I have some ideas \[\*\]).

Oh, and the types should definitely come before the terms.

\[\*\] In essence, ?*could be a special "fail" function, for which a guard ensures that it is never called. (You can think of it as being a function whose alpha type is constrained to be always empty.) This would be useful in other contexts in the input language. I wanted to bring this up at some point. No hurry, but it would be a nice feature. Other possible names for "?*" (in the input language) would be "fail" or "abort" or "avoid" or "block" or "bottom".

### Presentation of Functions

Irrespective of the above syntactic decision, a good question is how to present functions. There’s the "if then else" scheme, with equals and conjunctions:

    append = fun $xs : list. fun $ys : list.
      if $xs = Cons @uc_a_1 Nil && $ys = Cons @uc_a_0 Nil then
        Cons @uc_a_1 (Cons @uc_a_0 Nil)
      else if $xs = Cons @uc_a_0 Nil && $ys = Cons @uc_a_1 Nil then
        Cons @uc_a_0 (Cons @uc_a_1 Nil)
      else if $xs = Nil && $ys = Cons @uc_a_0 Nil then
        Cons @uc_a_0 Nil
      else if $xs = Nil && $ys = Cons @uc_a_1 Nil then
        Cons @uc_a_1 Nil
      else
        ?__ $xs $ys

Then there’s the ML-style tabular syntax, which has the definite advantage of compactness and readability. Also notice how the unspecified case does not have to be specified explicitly.

    append (Cons @uc_a_1 Nil) (Cons @uc_a_0 Nil) = Cons @uc_a_1 (Cons @uc_a_0 Nil)
    append (Cons @uc_a_0 Nil) (Cons @uc_a_1 Nil) = Cons @uc_a_0 (Cons @uc_a_1 Nil)
    append Nil (Cons @uc_a_0 Nil) = Cons @uc_a_0 Nil
    append Nil (Cons @uc_a_1 Nil) = Cons @uc_a_1 Nil

The main disadvantages are:

1.  It does not really scale up to higher-order logic. I.e. at some point, we’ll need to write out functions "(fun $xs. fun $ys. if …)" anyway.

2.  It is less uniform and requires more interfacing for each frontend.

So the "if then else" scheme is probably the best one. Also, users will rarely inspect the model of functions (e.g. nobody would look at the model of "append" in practice, unless they suspect a bug), except when these functions are free variables in the goal (for higher-order problems).

### Self-Contained or Not?

Should the output be self-contained — i.e., should it repeat declarations from the input, e.g. "data"? Repeating is what TSTP and CVC4 do. This can be interesting because then the output is potentially itself an input file, which is useful for testing (checking that the model is indeed a model by rerunning Nunchaku on the output) and connecting tools together. But it also means more clutter.

### Generated Names

We need to do something about the names of atoms and the names of bound variables. For atoms, there should be a clear naming convention enforced by Nunchaku, irrespective of what CVC4 does. For example, if an uninterpreted type is called `elem`, the atoms might be called `@elem\_1`, `@elem\_2`, …, `@elem\_N` or `elem@0`, `elem@1`, …, `elem@N-1`. Right now, CVC4 sometimes uses the name of some constant, and sometimes it generates some identifiers.

For bound variables, aggressive renaming is also the way to go. Perhaps the same convention as for atoms can be used, but with, say, "$" instead of "@".

## Current Situation

The current output is broken in some cases. Take "bugs/rec\_model.nun":

```
val a : type.

data list :=
  Nil
| Cons a list.

rec append : list -> list -> list :=
  forall (zs : list). append Nil zs = zs;
  forall (x : a) (ws : list) (zs : list). append (Cons x ws) zs = Cons x (append ws zs).

val xs : list.
val ys : list.

goal ~ (append xs ys = append ys xs).
```

Nunchaku’s output is currently

```
SAT:
  (model
     (terms
        ((ys Cons @uc_a_1 Nil)
         (xs Cons @uc_a_0 Nil)
         (append
            fun ($x1:list).
              fun ($x2:list).
                if
                  (($x1
                    =
                    (if (@uc_G_append_3 = $x1)
                     then Nil
                     else
                       if (@uc_G_append_2 = $x1)
                       then Nil
                       else
                         if (@uc_G_append_1 = $x1)
                         then Cons @uc_a_1 Nil
                         else Cons @uc_a_0 Nil))
                   &&
                   ($x2
                    =
                    (if (@uc_G_append_1 = $x1)
                     then Cons @uc_a_0 Nil
                     else
                       if (@uc_G_append_3 = $x1)
                       then Cons @uc_a_0 Nil
                       else Cons @uc_a_1 Nil)))
                then Cons @uc_a_1 (Cons @uc_a_0 Nil)
                else
                  if
                    (($x1
                      =
                      (if (@uc_G_append_3 = $x1)
                       then Nil
                       else
                         if (@uc_G_append_2 = $x1)
                         then Nil
                         else
                           if (@uc_G_append_1 = $x1)
                           then Cons @uc_a_1 Nil
                           else Cons @uc_a_0 Nil))
                     &&
                     ($x2
                      =
                      (if (@uc_G_append_1 = $x1)
                       then Cons @uc_a_0 Nil
                       else
                         if (@uc_G_append_3 = $x1)
                         then Cons @uc_a_0 Nil
                         else Cons @uc_a_1 Nil)))
                  then Cons @uc_a_1 (Cons @uc_a_0 Nil)
                  else
                    if
                      (($x1
                        =
                        (if (@uc_G_append_3 = $x1)
                         then Nil
                         else
                           if (@uc_G_append_2 = $x1)
                           then Nil
                           else
                             if (@uc_G_append_1 = $x1)
                             then Cons @uc_a_1 Nil
                             else Cons @uc_a_0 Nil))
                       &&
                       ($x2
                        =
                        (if (@uc_G_append_1 = $x1)
                         then Cons @uc_a_0 Nil
                         else
                           if (@uc_G_append_3 = $x1)
                           then Cons @uc_a_0 Nil
                           else Cons @uc_a_1 Nil)))
                    then Cons @uc_a_1 (Cons @uc_a_0 Nil)
                    else
                      if
                        (($x1
                          =
                          (if (@uc_G_append_3 = $x1)
                           then Nil
                           else
                             if (@uc_G_append_2 = $x1)
                             then Nil
                             else
                               if (@uc_G_append_1 = $x1)
                               then Cons @uc_a_1 Nil
                               else Cons @uc_a_0 Nil))
                         &&
                         ($x2
                          =
                          (if (@uc_G_append_1 = $x1)
                           then Cons @uc_a_0 Nil
                           else
                             if (@uc_G_append_3 = $x1)
                             then Cons @uc_a_0 Nil
                             else Cons @uc_a_1 Nil)))
                      then Cons @uc_a_1 (Cons @uc_a_0 Nil)
                      else ?__))
     (types ((a {@uc_a_1, @uc_a_0})))
  ))
```

The symbols `@uc_G_append_3` etc. have no business in there.

The model given by CVC4 looks like this:

```
(define-fun __nun_card_witness_1 () G_append @uc_G_append_0)
(define-fun append (($x1 list) ($x2 list)) list (ite (and (= $x1 (Cons @uc_a_1 (Cons @uc_a_0 (Cons @uc_a_0 Nil)))) (= $x2 (Cons @uc_a_1 Nil))) (Cons @uc_a_0 (Cons @uc_a_0 (Cons @uc_a_0 Nil))) (ite (and (= $x1 (Cons @uc_a_1 (Cons @uc_a_0 (Cons @uc_a_0 Nil)))) (= $x2 (Cons @uc_a_0 Nil))) (Cons @uc_a_2 (Cons @uc_a_0 Nil)) (ite (and (= $x1 (Cons @uc_a_1 Nil)) (= $x2 (Cons @uc_a_0 Nil))) (Cons @uc_a_1 (Cons @uc_a_0 Nil)) (ite (and (= $x1 Nil) (= $x2 (Cons @uc_a_1 Nil))) (Cons @uc_a_1 Nil) (ite (and (= $x1 Nil) (= $x2 (Cons @uc_a_0 Nil))) (Cons @uc_a_0 Nil) (Cons @uc_a_0 (Cons @uc_a_1 Nil))))))))
(define-fun proj_G_append_0 (($x1 G_append)) list (ite (= @uc_G_append_3 $x1) Nil (ite (= @uc_G_append_2 $x1) Nil (ite (= @uc_G_append_1 $x1) (Cons @uc_a_0 Nil) (Cons @uc_a_1 Nil)))))
(define-fun proj_G_append_1 (($x1 G_append)) list (ite (= @uc_G_append_1 $x1) (Cons @uc_a_1 Nil) (ite (= @uc_G_append_3 $x1) (Cons @uc_a_1 Nil) (Cons @uc_a_0 Nil))))
(define-fun ys () list (Cons @uc_a_0 Nil))
(define-fun xs () list (Cons @uc_a_1 Nil))
)
```

Once we filter out `proj_G_append_*`, this is almost already a good model for Nunchaku, except that we need to massage the "append" model so that it states clearly for all legal arguments what the value is and `?*_` otherwise. Looking at `proj_G_append**`, we see the different legal tuples of arguments:

```
@uc_G_append_0 = (Cons @uc_a_1 Nil, Cons @uc_a_0 Nil)
@uc_G_append_1 = (Cons @uc_a_0 Nil, Cons @uc_a_1 Nil)
@uc_G_append_2 = (Nil, Cons @uc_a_0 Nil)
@uc_G_append_3 = (Nil, Cons @uc_a_1 Nil)
```

So we already know that the "append" model is going to be of the form

```
append = fun $xs : list. fun $ys : list.
  if $xs = X1 && $ys = Y1 then
    Z1
  else if $xs = X2 && $ys = Y2 then
    Z2
  else if $xs = X3 && $ys = Y3 then
    Z3
  else if $xs = X4 && $ys = Y4 then
    Z4
  else
    ?__ $xs $ys
```

Notice the arguments to `?__`: They indicate the dependency of the unspecified value on its arguments. (One of my regrets with Nitpick is that I used the `…` notation for lots of things, resulting in an unclear notion of partial model.)

Now we plug in the values from the `@uc_G_append_*` tuples given above for the "Xs" and "Ys":

```
append = fun $xs : list. fun $ys : list.
  if $xs = Cons @uc_a_1 Nil && $ys = Cons @uc_a_0 Nil then
    Z1
  else if $xs = Cons @uc_a_0 Nil && $ys = Cons @uc_a_1 Nil then
    Z2
  else if $xs = Nil && $ys = Cons @uc_a_0 Nil then
    Z3
  else if $xs = Nil && $ys = Cons @uc_a_1 Nil then
    Z4
  else
    ?__ $xs $ys
```

Now we perform a lookup in the model of "append" generated by CVC4. The model looks like this (with better indentation than above):

```
append = fun $x1 : list. fun $x2 : list.
  ite (and (= $x1 (Cons @uc_a_1 (Cons @uc_a_0 (Cons @uc_a_0 Nil)))) (= $x2 (Cons @uc_a_1 Nil)))
    (Cons @uc_a_0 (Cons @uc_a_0 (Cons @uc_a_0 Nil)))
    (ite (and (= $x1 (Cons @uc_a_1 (Cons @uc_a_0 (Cons @uc_a_0 Nil)))) (= $x2 (Cons @uc_a_0 Nil)))
      (Cons @uc_a_2 (Cons @uc_a_0 Nil))
      (ite (and (= $x1 (Cons @uc_a_1 Nil)) (= $x2 (Cons @uc_a_0 Nil)))
        (Cons @uc_a_1 (Cons @uc_a_0 Nil))
        (ite (and (= $x1 Nil) (= $x2 (Cons @uc_a_1 Nil)))
          (Cons @uc_a_1 Nil)
          (ite (and (= $x1 Nil) (= $x2 (Cons @uc_a_0 Nil)))
            (Cons @uc_a_0 Nil)
            (Cons @uc_a_0 (Cons @uc_a_1 Nil))))))))
```

Notice that the first two branches are completely superfluous — they’re pure junk. We never look these up, so that’s OK. Filling in the values, we get:

```
append = fun $xs : list. fun $ys : list.
  if $xs = Cons @uc_a_1 Nil && $ys = Cons @uc_a_0 Nil then
    Cons @uc_a_1 (Cons @uc_a_0 Nil)   (* 3rd case above *)
  else if $xs = Cons @uc_a_0 Nil && $ys = Cons @uc_a_1 Nil then
    Cons @uc_a_0 (Cons @uc_a_1 Nil)   (* 6th case above)
  else if $xs = Nil && $ys = Cons @uc_a_0 Nil then
    Cons @uc_a_0 Nil   (* 5th case above *)
  else if $xs = Nil && $ys = Cons @uc_a_1 Nil then
    Cons @uc_a_1 Nil   (* 4th case above *)
  else
    ?__ $xs $ys
```

If cases are identical (whether or not they are consecutive), they should be merged into one condition. E.g.:

```
append = fun $xs : list. fun $ys : list.
  if $xs = Nil && $ys = Cons @uc_a_0 Nil ||
     $xs = Cons @uc_a_0 Nil && $ys = Nil then
    Cons @uc_a_1 (Cons @uc_a_0 Nil)
  else
    ...
```

In the above, I have indented "if then else" chains in a flat fashion, which is my favorite style. But I don’t mind too much if Nunchaku’s output indents differently (since few users will be exposed directly to it).
