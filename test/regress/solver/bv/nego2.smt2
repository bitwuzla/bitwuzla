(set-logic QF_BV)
(set-info :status unsat)
(declare-const v (_ BitVec 6))
(assert (and (= (bvneg v) #b100000) (not (bvnego v))))
(check-sat)

