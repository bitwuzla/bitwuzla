(set-logic QF_BV)
(assert (= ((_ repeat 3) (_ bv0 1)) (_ bv0 3)))
(assert (= ((_ repeat 4) (_ bv10 4)) (_ bv43690 16)))
(check-sat)

