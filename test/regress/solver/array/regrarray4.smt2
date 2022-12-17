(set-info :status sat)
(declare-const R (_ BitVec 8))
(declare-fun m () (Array (_ BitVec 8) (_ BitVec 8)))
(assert
 (=
  (_ bv1 1)
  (ite
   (not
    (=
     (bvor
      (bvshl (_ bv1 8) (select m R))
      (bvor (_ bv0 8) (select m R)))
     (bvor
      (bvor (_ bv0 8) (select m R))
      (bvshl (_ bv1 8) (select (store m (select m (_ bv0 8)) (_ bv0 8)) R))
     )
    ))
   (_ bv1 1)
   (_ bv0 1)
   )))
(check-sat)
