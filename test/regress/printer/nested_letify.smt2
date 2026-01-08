(assert
 (forall ((y (_ BitVec 2)))
 (let ((_let0 (bvadd y y)))
  (or
   (= y (bvmul _let0 _let0))
   (forall ((x (_ BitVec 3)))
   (let ((_let1 (bvadd x x)))
   (and
    (= x (bvmul _let1 _let1))
    (distinct y _let0)
   )
   )
   )
  )
 )
 )
)
(check-sat)
