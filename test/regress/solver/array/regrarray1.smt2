(set-info :status unsat) 
(declare-fun m () (Array (_ BitVec 8) (_ BitVec 8)))
(assert
 (and
  (= (_ bv0 8) (bvand (_ bv1 8) (select m (_ bv0 8))))
  (= (_ bv1 8) (bvand (_ bv1 8) (select m (bvand (_ bv1 8) (select m (bvand (_ bv1 8) (select m (_ bv0 8))))))))))
(check-sat)
