(set-info :status sat)
(declare-const x Bool)
(assert (or (exists ((? (_ BitVec 32))) false) (exists ((y (_ BitVec 32))) (or (forall ((y4 (_ BitVec 32))) x) (exists ((y2 (_ BitVec 32))) (or (exists ((y4 (_ BitVec 32))) (bvsgt y2 (_ bv0 32))) (forall ((? (_ BitVec 32))) (exists ((y4 (_ BitVec 32))) (= (bvadd ? y) (_ bv0 32))))))))))
(check-sat)
