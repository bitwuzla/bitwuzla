(set-option :incremental false)
(set-logic QF_BV)
(assert (= (bvshl (_ bv0 1) (_ bv0 1)) (_ bv0 1)))
(assert (= (bvshl (_ bv0 1) (_ bv1 1)) (_ bv0 1)))
(assert (= (bvshl (_ bv1 1) (_ bv0 1)) (_ bv1 1)))
(assert (= (bvshl (_ bv1 1) (_ bv1 1)) (_ bv0 1)))
(check-sat)

