(set-option :pp-quant true)
(assert (forall ((c (_ BitVec 32))) (forall ((__ (_ BitVec 32))) (forall ((c_ (_ BitVec 32))) (not (= c_ (bvsub __ (bvsub (_ bv1 32) c))))))))
(set-info :status unsat)
(check-sat)
