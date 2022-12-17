(set-info :status sat)
(declare-const f (_ BitVec 1))
(assert (= (_ bv0 58) ((_ zero_extend 57) (bvnot (bvcomp (_ bv0 109) (bvurem (concat (_ bv1 53) (_ bv0 56)) ((_ zero_extend 56) ((_ zero_extend 52) f))))))))
(check-sat)
