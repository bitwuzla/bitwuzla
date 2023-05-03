(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(assert (not (= (bvudiv s (_ bv0 32)) (bvnot (_ bv0 32)))))
(check-sat)

