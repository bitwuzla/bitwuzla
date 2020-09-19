(set-option :incremental false)
(set-info :status sat)
(set-logic QF_BV)
(declare-fun a () Bool)
(assert (not a))
(check-sat)

