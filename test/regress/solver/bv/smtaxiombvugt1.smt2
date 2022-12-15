
(set-logic QF_BV)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
