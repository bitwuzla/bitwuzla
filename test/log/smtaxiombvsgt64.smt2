
(set-logic QF_BV)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))
(assert (not (= (bvsgt s t) (bvslt t s))))
(check-sat)
(exit)
