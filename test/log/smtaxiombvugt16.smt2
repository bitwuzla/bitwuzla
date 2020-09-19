
(set-logic QF_BV)
(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))
(assert (not (= (bvugt s t) (bvult t s))))
(check-sat)
(exit)
