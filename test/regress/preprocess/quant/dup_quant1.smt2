(set-logic BV)
(declare-const x (_ BitVec 8))
(declare-const z (_ BitVec 8))
(define-fun P () Bool
  (or (forall ((y (_ BitVec 8))) (not (= (bvadd x y) (_ bv0 8)))) (bvult x z)))
(assert P)
(assert P)
(check-sat)
