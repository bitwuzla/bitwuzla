(set-info :status sat)
(declare-fun v () (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))
(assert (= (_ bv1 32) (select (select v (_ bv1 32)) (_ bv0 32))))
(check-sat)
