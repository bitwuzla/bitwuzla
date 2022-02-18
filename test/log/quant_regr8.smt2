(set-info :status unsat)
(declare-const t (_ BitVec 2))
(assert (distinct (exists ((x (_ BitVec 4))) (= ((_ zero_extend 2) t) (bvashr x ((_ zero_extend 2) t)))) (or (= (_ bv0 4) ((_ zero_extend 2) t)) (exists ((i (_ BitVec 4))) (and (= i (_ bv0 4)) (bvult (_ bv0 4) (ite (= (_ bv0 1) ((_ extract 1 1) t)) (_ bv1 4) (_ bv0 4))))))))
(check-sat)
