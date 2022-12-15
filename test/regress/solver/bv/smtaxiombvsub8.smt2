
(set-logic QF_BV)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(assert (not (= (bvsub s t) (bvadd s (bvneg t)))))
(check-sat)
(exit)
