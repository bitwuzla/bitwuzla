(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 8))
(declare-const v1 (_ BitVec 8))
(assert (= #b1 (bvor (bvnot (ite (bvuge (bvor v0 v1) (ite (= (bvugt v0 v1) #b1) v0 v1)) #b1 #b0)) (bvnot (bvule (bvand v0 v1) (ite (= (bvugt v0 v1) #b1) v0 v1))))))
(check-sat)