(set-info :status unsat)
(assert (and (exists ((? (_ BitVec 32))) true) (forall ((? (_ BitVec 32))) (and true (forall ((y (_ BitVec 32))) (and true (forall ((y6 (_ BitVec 32))) (bvslt y (_ bv0 32)))))))))
(check-sat)
