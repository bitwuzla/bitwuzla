
(set-logic QF_BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
