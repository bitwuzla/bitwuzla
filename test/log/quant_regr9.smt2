(assert (and true (forall ((v_ (_ BitVec 32))) (or (exists ((m (_ BitVec 32))) (and (= v_ m) (distinct m (_ bv0 32)))) (forall ((v (_ BitVec 32))) (or (distinct v_ v) (= v (_ bv0 32))))))))
(check-sat)
