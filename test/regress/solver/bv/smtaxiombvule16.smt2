
(set-logic QF_BV)
(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))
(assert (not (= (bvule s t) (or (bvult s t) (= s t)))))
(check-sat)
(exit)
