(set-info :status sat)
(declare-const v0 (_ BitVec 3))
(assert (= (_ bv0 3) (bvadd (bvshl (bvshl (_ bv7 3) v0) v0) (bvshl (_ bv7 3) v0))))
(check-sat)
