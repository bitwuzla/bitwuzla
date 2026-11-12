(declare-const a (_ BitVec 26))
(declare-const b Bool)
(declare-const rm RoundingMode)
(declare-fun f (Bool (_ BitVec 55)) Bool)
(define-fun za () (_ BitVec 55) ((_ zero_extend 29) a))
(define-fun o () Bool (bvumulo (_ bv16465860569848920 55) za))
(assert
  (distinct RNE
    (ite (and o
              (forall ((r RoundingMode))
                (= b (and (bvumulo (_ bv981441770 55) za)
                          (distinct b
                            (not (= b (f (bvumulo za (ite o (_ bv1 55) (_ bv0 55)))
                                         (_ bv0 55)))))))))
         RTP
         rm)))
(set-info :status sat)
(check-sat-assuming ((bvumulo (_ bv981441770 55) za)))
(set-info :status sat)
(check-sat)
