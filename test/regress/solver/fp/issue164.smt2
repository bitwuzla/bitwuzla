(set-logic QF_FP)
(assert (fp.lt (fp (_ bv0 1) (_ bv0 5) (_ bv0 10)) (fp.div RTN ((_ to_fp 5 11) RNA (_ bv323 16)) (fp (_ bv0 1) (_ bv0 5) (_ bv1 10)))))
(set-info :status sat)
(check-sat)
