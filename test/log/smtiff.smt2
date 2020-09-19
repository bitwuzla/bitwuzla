(set-option :incremental false)
(set-logic QF_BV)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (and (not a) (= a b)))
(check-sat)

