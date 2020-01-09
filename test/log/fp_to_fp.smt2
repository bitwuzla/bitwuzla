(set-logic QF_FP)
(define-fun x () Float16 (_ +zero 5 11))
(assert (= x ((_ to_fp 5 11) (_ bv0 16))))
(check-sat)
