(set-option :incremental false)
(set-logic QF_BV)
(assert (not (= (_ bv255 8) (bvnot (_ bv0 8)))))
(check-sat)

