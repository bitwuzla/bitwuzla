(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert
    (distinct
        ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
        ((_ extract 3 0) (bvashr y (_ bv1 8)))))
(check-sat)
(get-model)
(get-value (x y (bvmul x x)))
(exit)
