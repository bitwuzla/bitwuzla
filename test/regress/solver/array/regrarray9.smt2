(set-info :status sat)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(assert (or (not (= (_ bv0 4) (select a (_ bv0 4)))) (not (= a (store (store a (_ bv0 4) (select a (_ bv1 4))) (_ bv1 4) (select a (_ bv0 4)))))))
(check-sat)
