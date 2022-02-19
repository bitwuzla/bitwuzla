(declare-const x Bool)
(assert (or (forall ((? (_ BitVec 32))) x) (and (exists ((? (_ BitVec 32))) true) (forall ((? (_ BitVec 32))) (and x (forall ((y (_ BitVec 32))) (and true (forall ((y6 (_ BitVec 32))) (bvslt (_ bv0 32) (bvadd y ?))))))))))
(check-sat)
