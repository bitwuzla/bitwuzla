(set-info :status sat)
(declare-const T (_ BitVec 1))
(assert (bvsge (bvadd (_ bv1 32) (bvmul (_ bv4294967295 32) (bvadd (_ bv1 32) ((_ zero_extend 31) T) (bvmul (_ bv4294967295 32) ((_ zero_extend 31) T))))) (_ bv0 32)))
(check-sat)
