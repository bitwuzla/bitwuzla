(declare-const s (_ BitVec 1))
(assert (= (_ bv0 4) (bvadd (_ bv3 4) (bvor (_ bv1 4) ((_ zero_extend 3) s)))))
(set-info :status unsat)
(check-sat)
