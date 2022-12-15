(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (and (= (bvredxor x) (_ bv1 1)) (= ((_ extract 7 4) x) (_ bv0 4))))
(check-sat)
