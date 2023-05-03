(set-info :status unsat)
(set-logic QF_BV)
(declare-fun a () Bool)
(assert (and a (not a)))
(check-sat)

