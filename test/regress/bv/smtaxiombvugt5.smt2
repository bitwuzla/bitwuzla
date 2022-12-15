
(set-logic QF_BV)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
