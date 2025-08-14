; outcome: timeout
; expected: sat

; Nitpick can do it very fast by keeping all cardinalities synchronized, and taking them to be all
; 2. CVC4 is spinning.

(set-option :produce-models true)
(set-option :interactive-mode true)
(set-logic ALL_SUPPORTED)
(declare-sort g_ 0)
(declare-sort f_ 0)
(declare-sort e_ 0)
(declare-datatypes ()
   ((prod1_ (Pair1_ (_select_Pair1__0 e_) (_select_Pair1__1 f_)))))
(declare-sort d_ 0)
(declare-sort c_ 0)
(declare-sort b_ 0)
(declare-sort a_ 0)
(declare-datatypes ()
   ((prod_ (Pair_ (_select_Pair__0 a_) (_select_Pair__1 b_)))))
(declare-fun f1_ (prod_ c_ d_ prod1_) g_)
(declare-fun g1_ (prod_ d_) c_)
(declare-fun h_ (prod_) prod1_)
(declare-fun nun_sk_0_ () prod_)
(declare-fun nun_sk_1_ (c_) d_)
(assert
 (not
  (exists ((v/34 c_))
     (exists ((x/35 prod1_))
        (= (f1_ nun_sk_0_ v/34 (nun_sk_1_ v/34) x/35)
         (f1_ nun_sk_0_ (g1_ nun_sk_0_ (nun_sk_1_ v/34)) (nun_sk_1_ v/34) 
          (h_ nun_sk_0_)))))))
(check-sat)
