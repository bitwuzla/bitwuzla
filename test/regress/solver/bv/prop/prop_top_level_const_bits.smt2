(set-info :status sat)
(declare-const I (_ BitVec 8))
(declare-fun R () (_ BitVec 8))
(assert
  (and
    (=
      (_ bv0 8)
      (bvsub (_ bv1 8) (bvor R I))
    )
    (not
      (=
        (_ bv0 8)
        (bvand (_ bv1 8) (bvor R I))
      )
    )
  )
)
(check-sat)
