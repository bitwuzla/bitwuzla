(set-info :status sat)
(declare-const x Bool)
(assert
 (or
  (forall ((y1 (_ BitVec 32))) x)
   (forall ((z (_ BitVec 32)))
    (and x
     (forall ((y2 (_ BitVec 32)))
       (forall ((y3 (_ BitVec 32)))
        (bvslt (_ bv0 32) (bvadd y2 z))))))))
(check-sat)
