
(set-logic QF_BV)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(assert (not (= (bvsgt s t) (bvslt t s))))
(check-sat)
(exit)
