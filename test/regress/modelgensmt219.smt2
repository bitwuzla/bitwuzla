(set-logic QF_BV)
(define-fun $e1 () (_ BitVec 1) (_ bv0 1))
(assert (not (= (bvnot $e1) #b0)))
(check-sat)
(exit)