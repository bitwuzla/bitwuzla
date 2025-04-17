(set-info :status unsat)
(declare-const v (_ BitVec 1))
(assert (= (_ bv0 1) (ite (bvult (_ bv0 2) ((_ zero_extend 1) ((_ extract 2 2) (bvnot (bvadd (_ bv1 3) ((_ zero_extend 2) v) ((_ zero_extend 2) v)))))) (_ bv1 1) (_ bv0 1))))
(check-sat)
