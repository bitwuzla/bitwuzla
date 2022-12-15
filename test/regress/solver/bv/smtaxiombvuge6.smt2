
(set-logic QF_BV)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(assert (not (= (bvuge s t) (or (bvult t s) (= s t)))))
(check-sat)
(exit)
