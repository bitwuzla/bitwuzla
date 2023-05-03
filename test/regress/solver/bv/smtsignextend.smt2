(set-logic QF_BV)
(set-info :status sat)
(assert (= ((_ sign_extend 2) (_ bv2 2)) (_ bv14 4)))
(check-sat)

