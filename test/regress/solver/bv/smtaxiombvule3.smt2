
(set-logic QF_BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(assert (not (= (bvule s t) (or (bvult s t) (= s t)))))
(check-sat)
(exit)
