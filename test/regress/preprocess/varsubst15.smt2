(set-info :status sat)
(declare-const x Bool)
(assert (or (forall ((? (_ BitVec 16))) x) (forall ((? (_ BitVec 16))) x)))
(check-sat)
