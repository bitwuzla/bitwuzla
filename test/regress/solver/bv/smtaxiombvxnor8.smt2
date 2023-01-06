(set-logic QF_BV)
(set-info :status unsat)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(assert (not (= (bvxnor s t) (bvor (bvand s t) (bvand (bvnot s) (bvnot t))))))
(check-sat)
(exit)