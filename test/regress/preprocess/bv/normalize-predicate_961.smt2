(declare-const i (_ BitVec 1))
(set-info :status sat)
(assert (= (_ bv0 1) (ite (= (_ bv0 64) (bvsub (bvadd (_ bv1 64) (_ bv1 64) ((_ zero_extend 32) ((_ zero_extend 24) ((_ zero_extend 7) i)))) (bvadd (_ bv1 64) ((_ zero_extend 32) ((_ zero_extend 24) ((_ zero_extend 7) i))) ((_ zero_extend 32) (bvsub (_ bv1 32) ((_ zero_extend 24) ((_ zero_extend 7) i))))))) (_ bv1 1) (_ bv0 1))))
(check-sat)
