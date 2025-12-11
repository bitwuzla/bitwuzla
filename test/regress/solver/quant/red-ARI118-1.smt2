(set-option :quant-ic true)
(assert (forall ((? (_ BitVec 32))) (not (= ? (bvmul ? ?)))))
(set-info :status unsat)
(check-sat)
