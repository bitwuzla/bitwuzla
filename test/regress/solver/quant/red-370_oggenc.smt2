(set-option :quant-ic true)
(assert (and true (forall ((u (_ BitVec 32)) (n (_ BitVec 32))) (and (= u (_ bv0 32)) (= (concat u (_ bv0 1)) (bvadd (concat n (_ bv1 1)) (bvmul (_ bv8589934591 33) (concat u (_ bv1 1)))))))))
(set-info :status unsat)
(check-sat)
