(set-logic QF_BV)
(define-fun x ((y Bool) (z Bool)) Bool y)
(define-const x Bool true)
(assert (x false true))
(check-sat)

