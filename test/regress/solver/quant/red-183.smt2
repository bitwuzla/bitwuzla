(set-option :quant-ic true)
(assert (and true (forall ((V (_ BitVec 32))) (and (= V (_ bv0 32)) (= (_ bv0 32) (bvadd V (bvmul V V)))))))
(set-info :status unsat)
(check-sat)
