
(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))
(assert (not (= (bvsgt s t) (bvslt t s))))
(check-sat)
(exit)
