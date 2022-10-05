(set-info :status sat)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c (_ BitVec 3))
(assert
 (or
  a
  (and
   b
   (exists ((y (_ BitVec 3)))
    (or
     (= c (_ bv0 3))
     (forall ((x (_ BitVec 3))) (bvsle (bvadd y x) (_ bv0 3))))))))
(check-sat)
