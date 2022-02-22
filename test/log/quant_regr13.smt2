(set-info :status sat)
(assert (and (forall ((? (_ BitVec 32))) true) (exists ((? (_ BitVec 32))) (and (forall ((y (_ BitVec 32))) (bvsge ? (_ bv0 32))) (exists ((y (_ BitVec 32))) (forall ((? (_ BitVec 32))) (= y (_ bv0 32))))))))
(check-sat)
