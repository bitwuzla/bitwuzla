(declare-const m (_ BitVec 2))
(declare-const x Bool)
(assert (forall ((t (_ BitVec 32))) (and x (bvsle t (_ bv0 32)) (= (_ bv0 32) ((_ zero_extend 30) m)))))
(check-sat)
