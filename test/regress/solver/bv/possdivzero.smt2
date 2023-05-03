(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(assert (bvsge s (_ bv0 4)))
(assert (not (= (bvsdiv s (_ bv0 4)) (bvnot (_ bv0 4)))))
(check-sat)

