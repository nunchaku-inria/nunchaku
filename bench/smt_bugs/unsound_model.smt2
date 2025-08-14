; outcome: sat with a model where 'x = y'
; expected: sat with a different model (see also comment further down)

; cvc4 --finite-model-find unsound_model.smt2

; AR's answer: Use --mbqi=none for now.

(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)

(declare-sort a 0)
(declare-datatypes () ((tree (Leaf (lab a)))))

(declare-sort alpha 0)
(declare-fun alphabet (tree a) Bool)
(declare-fun g1 (alpha) tree)
(declare-fun g2 (alpha) a)

(assert
 (forall ((x alpha))
    (=>
     (= (lab (g1 x)) (g2 x))
     (alphabet (g1 x) (g2 x)))))

(declare-fun x () a)
(declare-fun y () a)

; The problem gets unsat with this assert. However, "x = y" holds in the
; generated model!
;
; (assert (= x y))

(assert
  (and
   (exists ((b alpha)) (and (= (Leaf y) (g1 b)) (= x (g2 b))))
   (not (alphabet (Leaf y) x))))

(check-sat)
(get-model)
