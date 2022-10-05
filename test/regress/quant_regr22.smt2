(set-info :status sat)
(declare-const a Bool)
(assert
 (or
  a
  (exists ((y (_ BitVec 16)))
   (forall ((x1 (_ BitVec 16)))
    (forall ((x2 (_ BitVec 16)))
     (and a
      (forall ((x3 (_ BitVec 16)))
       (bvsgt (_ bv0 16) (bvadd x3 x2 x1 y)))))))))
(check-sat)
