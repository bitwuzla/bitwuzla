(set-info :status sat)
(declare-const a Bool)
(declare-const b Bool)
(assert
 (or a
  (exists ((y (_ BitVec 1)))
   (forall ((x1 (_ BitVec 1)))
    (or
     b
     (forall ((x2 (_ BitVec 1))) (distinct (_ bv0 1) (bvadd (_ bv1 1) y x1 x2))))))))
(check-sat)
