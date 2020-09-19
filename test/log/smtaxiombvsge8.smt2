
(set-logic QF_BV)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(assert (not (= (bvsge s t) (bvsle t s))))
(check-sat)
(exit)
