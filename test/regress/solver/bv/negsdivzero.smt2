(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(assert (bvslt s (_ bv0 4)))
(assert (not (= (bvsdiv s (_ bv0 4)) (_ bv1 4))))
(check-sat)

