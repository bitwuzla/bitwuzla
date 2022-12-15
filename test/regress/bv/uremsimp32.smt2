(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 32))
(declare-fun v2 () (_ BitVec 32))
(declare-fun v3 () (_ BitVec 32))
(assert (and (not (= v1 (_ bv0 32))) (= v3 (bvurem v2 v1)) (not (bvult v3 v1))))
(check-sat)

