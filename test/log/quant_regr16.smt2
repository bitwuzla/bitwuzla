(declare-const x Bool)
(assert (or (forall ((? (_ BitVec 32))) x) (and (exists ((? (_ BitVec 32))) true) (forall ((? (_ BitVec 32))) (and x (forall ((y (_ BitVec 32))) (and (not (= ? (_ bv1 32))) (forall ((y6 (_ BitVec 32))) (bvslt (_ bv0 32) (bvadd y6 y ?))))))))))
(check-sat)
