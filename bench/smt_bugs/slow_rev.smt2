; outcome: timeout
; expected: sat within 1 s (see also comment near the end of the file)

; cvc4 --finite-model-find --fmf-fun slow_rev.smt2 

(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)

(declare-sort a 0)
(declare-datatypes () ((prod (Pair (fst a) (snd a)))))
(declare-datatypes () ((plist (PCons (phd prod) (ptl plist)) (PNil))))
(declare-datatypes () ((list (Cons (hd a) (tl list)) (Nil))))

(define-fun-rec zip ((xs list) (ys list)) plist
  (ite (is-Cons xs)
    (ite (is-Cons ys)
      (PCons (Pair (hd xs) (hd ys)) 
       (zip (tl xs) (tl ys)))
      PNil)
    PNil))
(define-fun-rec append ((xs list) (ys list)) list
  (ite (is-Cons xs)
    (Cons (hd xs) 
     (append (tl xs) ys))
    ys))
(define-fun-rec rev ((xs list)) list
  (ite (is-Cons xs)
    (append (rev (tl xs)) 
     (Cons (hd xs) Nil))
    Nil))

(declare-fun xs () list)
(declare-fun ys () list)
(declare-fun y () a)
(declare-fun x () a)
(assert (not (= x y)))

; The problem becomes easy with the following line:
; (assert (= xs (Cons y Nil)))
(assert (not (= (zip (Cons x xs) ys) (zip (rev (Cons x xs)) (rev ys)))))
(check-sat)
