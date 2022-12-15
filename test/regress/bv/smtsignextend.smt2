(set-option :incremental false)
(set-logic QF_BV)
(assert (= ((_ sign_extend 2) (_ bv2 2)) (_ bv14 4)))
(check-sat)

