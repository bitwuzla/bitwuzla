(set-logic BV)
(set-info :status sat)
(declare-const g (_ BitVec 2))
(declare-const h (_ BitVec 2))
(declare-const k (_ BitVec 2))
(define-fun block () Bool
  (forall ((o (_ BitVec 2)))
    (and (forall ((p (_ BitVec 2)) (q (_ BitVec 2))) (bvule (bvand p q) k))
         (bvule o k))))
(assert (not (forall ((x (_ BitVec 2)))
  (and (forall ((v (_ BitVec 2))) (bvule (bvadd v g) x))
       block
       (bvule x h)))))
(assert (forall ((x2 (_ BitVec 2)))
  (and (forall ((v2 (_ BitVec 2))) (bvule (bvadd v2 g) v2))
       block
       (bvule x2 h))))
(check-sat)
