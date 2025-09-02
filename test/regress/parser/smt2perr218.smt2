(define-fun interleave ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 4)
  (let
    ((a2 (bvshl ((_ zero_extend 2) a) (_ bv1 4))))
     ;(a3 (bvshl ((_ zero_extend 2) a) (_ bv1 4))))
    (let
      ((b4 ((_ zero_extend 2) b)))
      b4
    )
 a2)
  )
)
