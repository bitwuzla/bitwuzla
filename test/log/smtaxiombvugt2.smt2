
(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
