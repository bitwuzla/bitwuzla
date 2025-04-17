(set-info :status sat)
(declare-const T (_ BitVec 1))
(assert (= (_ bv0 32) (bvadd ((_ zero_extend 31) T) (bvmul ((_ zero_extend 31) T) (_ bv113 32) ((_ zero_extend 31) T) (_ bv113 32) (_ bv14 32) (_ bv56 32) (_ bv113 32) (_ bv3 32)))))
(check-sat)
