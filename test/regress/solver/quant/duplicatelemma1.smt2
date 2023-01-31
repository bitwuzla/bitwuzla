(declare-const __ (_ BitVec 2))
(declare-fun i () Float64)
(assert
 (forall ((v_ (_ BitVec 64)))
  (or
   (forall ((v (_ BitVec 32))) (not (bvugt ((_ extract 63 32) v_) (_ bv1073217536 32))))
   (not (= i (fp (_ bv0 1) ((_ extract 62 52) v_) ((_ extract 51 0) v_)))))))
(assert (bvugt ((_ zero_extend 30) __) (_ bv0 32)))
(set-info :status sat)
(check-sat)
