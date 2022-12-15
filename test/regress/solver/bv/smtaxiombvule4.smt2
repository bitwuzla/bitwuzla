
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(assert (not (= (bvule s t) (or (bvult s t) (= s t)))))
(check-sat)
(exit)
