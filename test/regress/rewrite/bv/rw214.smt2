(set-info :status unsat)
(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 2))
(declare-fun v0 () (_ BitVec 1))
(assert (not (= (bvand ((_ zero_extend 3) v0) ((_ sign_extend 1) (concat v1 (_ bv0 1)))) (_ bv0 4))))
(check-sat)

