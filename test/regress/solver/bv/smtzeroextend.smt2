(set-logic QF_BV)
(set-info :status sat)
(assert (= ((_ zero_extend 2) (_ bv2 2)) (_ bv2 4)))
(check-sat)

