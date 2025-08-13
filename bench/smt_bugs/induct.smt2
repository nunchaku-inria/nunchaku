; outcome: timeout
; expected: unsat

; cvc4 --quant-ind --lang smt induct.smt2

; I was hoping that CVC4 would notice that it can do an induction on "t", even
; though it is not bound by an "exists" in the conjecture. We prefer to
; Skolemize on our side to get more informative models.

(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)
(declare-datatypes () ((nat (Suc (pred nat)) (zero ))))
(declare-sort a 0)
(declare-fun nuncardwitness0 () a)
(declare-datatypes ()
   ((tree
       (Node (selectNode0 nat) 
          (selectNode1 tree) (selectNode2 tree)) 
       (Leaf (selectLeaf0 nat) (selectLeaf1 a)))))
(declare-fun plus (nat nat) nat)
(assert (forall ((n/102 nat)) (= (plus zero n/102) n/102)))
(assert
 (forall ((m/103 nat))
    (forall ((n/104 nat))
       (= (plus (Suc m/103) n/104) (Suc (plus m/103 n/104))))))
(declare-fun lesseq (nat nat) Bool)
(assert (forall ((n/105 nat)) (lesseq zero n/105)))
(assert
 (forall ((m/106 nat))
    (forall ((n/107 nat))
       (and
        (or (not (lesseq (Suc m/106) n/107)) 
         (and (is-Suc n/107) (lesseq m/106 (pred n/107)))) 
        (or (not (is-Suc n/107)) 
         (not (lesseq m/106 (pred n/107))) 
         (lesseq (Suc m/106) n/107))))))
(declare-fun max (nat nat) nat)
(assert
 (forall ((a2/108 nat))
    (forall ((b1/109 nat))
       (= (max a2/108 b1/109)
        (ite (lesseq a2/108 b1/109) b1/109 a2/108)))))
(declare-fun one () nat)
(assert (= one (Suc zero)))
(declare-fun height (tree) nat)
(assert
 (forall ((w/110 nat))
    (forall ((a2/111 a)) (= (height (Leaf w/110 a2/111)) zero))))
(assert
 (forall ((w/112 nat))
    (forall ((t1/113 tree))
       (forall ((t2/114 tree))
          (= (height (Node w/112 t1/113 t2/114))
           (plus (max (height t1/113) (height t2/114)) one))))))
(declare-fun t () tree)
(declare-fun swapLeaves (tree nat a nat a) tree)
(assert
 (forall ((wc/115 nat))
    (forall ((c/116 a))
       (forall ((wa1/117 nat))
          (forall ((a2/118 a))
             (forall ((wb1/119 nat))
                (forall ((b1/120 a))
                   (=
                    (swapLeaves (Leaf wc/115 c/116) wa1/117 a2/118 
                     wb1/119 b1/120)
                    (ite (= c/116 a2/118) (Leaf wb1/119 b1/120)
                      (ite (= c/116 b1/120) (Leaf wa1/117 a2/118)
                        (Leaf wc/115 c/116)))))))))))
(assert
 (forall ((w/121 nat))
    (forall ((t1/122 tree))
       (forall ((t2/123 tree))
          (forall ((wa1/124 nat))
             (forall ((a2/125 a))
                (forall ((wb1/126 nat))
                   (forall ((b1/127 a))
                      (=
                       (swapLeaves (Node w/121 t1/122 t2/123) 
                        wa1/124 a2/125 wb1/126 b1/127)
                       (Node w/121 
                        (swapLeaves t1/122 wa1/124 a2/125 wb1/126 
                         b1/127) 
                        (swapLeaves t2/123 wa1/124 a2/125 wb1/126 
                         b1/127)))))))))))
(declare-fun wa () nat)
(declare-fun a1 () a)
(declare-fun wb () nat)
(declare-fun b () a)
(assert (not (= (height (swapLeaves t wa a1 wb b)) (height t))))
(check-sat)
