(set-logic QF_BV)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(define-const interleave (_ BitVec 4)
  (let
    ((a2 (bvshl ((_ zero_extend 2) a) (_ bv1 4))))
    (let
      ((b4 ((_ zero_extend 2) b)))
      b4
    )
 a2)
  )
)
(check-sat)
