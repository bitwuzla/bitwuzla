(set-info :status unsat)
(declare-fun m () (_ BitVec 32))
(assert (forall ((t (_ BitVec 32))) (and (bvsle t (_ bv0 32)) (= m (_ bv1 32)))))
(check-sat)
