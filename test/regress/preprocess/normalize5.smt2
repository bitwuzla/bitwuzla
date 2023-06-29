(set-info :status unsat)
(define-fun f ((_f3_1 (_ BitVec 122)) (_f3_2 Bool)) Bool (bvsaddo _f3_1 (bvneg (bvdec (_ bv0 122)))))
(assert (f (bvdec (_ bv0 122)) (bvumulo (_ bv0 61) (_ bv0 61))))
(check-sat)
