(declare-const _let0 (_ BitVec 2))
(assert (= _let0 #b01))
(assert
 (forall ((y (_ BitVec 2)))
  (=> (bvult (bvadd y y) (bvnot (bvadd y y)))
      (= _let0 #b01))))
(check-sat)
