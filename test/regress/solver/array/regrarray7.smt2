(set-info :status sat)
(declare-const a (Array (_ BitVec 2) (_ BitVec 1)))
(assert (not (= a (store a (_ bv0 2) (_ bv0 1)))))
(check-sat)
