(set-logic QF_BV)
(declare-const x Bool)
(define-fun P ((x Bool) (x Bool)) Bool x)
(assert (P false true))
(check-sat)