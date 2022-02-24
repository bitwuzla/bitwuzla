(set-info :status unsat)
(declare-const x Bool)
(assert (and (exists ((y (_ BitVec 32))) true) (forall ((y (_ BitVec 32))) (and x (exists ((y2 (_ BitVec 32))) (forall ((? (_ BitVec 32))) (bvsle (_ bv0 32) (bvadd ? y2 y))))))))
(check-sat)
