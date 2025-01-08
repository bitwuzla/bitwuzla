(set-logic QF_BV)
(define-fun P ((x Bool) (x Bool)) Bool x)
(assert (P false true))
(check-sat)
