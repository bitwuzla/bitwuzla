(set-info :status unsat)
(declare-const T (_ BitVec 1))
(assert (not (= (_ bv0 32) ((_ zero_extend 31) T))))
(assert (bvule
         (bvadd ((_ zero_extend 31) T) ((_ zero_extend 31) T))
         (_ bv1 32)))
(check-sat)
