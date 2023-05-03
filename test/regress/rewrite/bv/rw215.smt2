(set-info :status unsat)
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 1))
(declare-fun v1 () (_ BitVec 2))
(declare-fun v2 () (_ BitVec 1))
(assert (and (not (= (bvand (concat v0 (_ bv0 1)) ((_ zero_extend 1) v2)) (_ bv0 2))) (not (distinct v1 ((_ zero_extend 1) v0)))))
(check-sat)

