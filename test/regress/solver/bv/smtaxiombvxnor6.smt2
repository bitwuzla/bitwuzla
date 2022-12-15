
(set-logic QF_BV)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(assert (not (= (bvxnor s t) (bvor (bvand s t) (bvand (bvnot s) (bvnot t))))))
(check-sat)
(exit)
