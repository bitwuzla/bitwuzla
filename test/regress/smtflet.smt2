(set-option :incremental false)
(set-logic QF_BV)
(declare-fun a () Bool)
(assert (and a (not a)))
(check-sat)

