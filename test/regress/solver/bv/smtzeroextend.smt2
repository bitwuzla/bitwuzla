(set-logic QF_BV)
(set-info :status sat)
(set-option :incremental false)
(assert (= ((_ zero_extend 2) (_ bv2 2)) (_ bv2 4)))
(check-sat)

