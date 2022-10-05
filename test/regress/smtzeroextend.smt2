(set-option :incremental false)
(set-logic QF_BV)
(assert (= ((_ zero_extend 2) (_ bv2 2)) (_ bv2 4)))
(check-sat)

