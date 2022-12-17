(set-info :status sat)
(declare-const x (_ BitVec 9))
(declare-fun t () (_ BitVec 9))
(declare-fun m () (Array (_ BitVec 9) (_ BitVec 8)))
(assert
 (and
  (= m (store m (_ bv1 9) (_ bv0 8)))
  (= (_ bv0 9) (bvsub (_ bv264 9) x))
  (=
   x
   (bvor ((_ zero_extend 1) (select m (_ bv0 9))) (bvshl ((_ zero_extend 1) (select (store m t (_ bv1 8)) (_ bv1 9))) (_ bv8 9))))))
(check-sat)
