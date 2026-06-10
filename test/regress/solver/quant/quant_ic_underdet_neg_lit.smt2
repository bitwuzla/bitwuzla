(set-logic BV)
(set-info :status sat)
(set-option :quant-ic true)
(set-option :quant-ic-underdet true)
(assert
  (not
    (and
      (not (forall ((i (_ BitVec 32))) true))
      (forall ((e (_ BitVec 32)))
        (not (forall ((h (_ BitVec 32)))
          (= (_ bv1 32) (bvmul h (_ bv2 32)))))))))
(check-sat)
(exit)
