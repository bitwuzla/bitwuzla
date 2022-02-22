(set-info :status unsat)
(assert (and (exists ((? (_ BitVec 32))) true) (exists ((? (_ BitVec 32))) (and true (forall ((y (_ BitVec 32))) (and (forall ((? (_ BitVec 32))) (bvslt ? (_ bv0 32))) (forall ((? (_ BitVec 32))) (bvslt y (_ bv0 32)))))))))
(check-sat)
