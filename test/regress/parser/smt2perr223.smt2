(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x ((_ repeat 0) x)))
(check-sat)
