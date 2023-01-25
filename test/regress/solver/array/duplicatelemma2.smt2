(declare-fun a () (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(assert
  (=
   (store a (_ bv0 1) b)
   (store a (_ bv0 1) (store b (_ bv1 1) (_ bv0 1)))
  )
)
(set-info :status sat)
(check-sat)
