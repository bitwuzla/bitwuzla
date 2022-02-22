(set-info :status sat)
(declare-const x Bool)
(assert (exists ((y1 (_ BitVec 32))) (and (forall ((? (_ BitVec 32))) x) (or false (exists ((y (_ BitVec 32))) (exists ((? (_ BitVec 32))) (bvslt (bvadd y y1) (_ bv0 32))))))))
(check-sat)
