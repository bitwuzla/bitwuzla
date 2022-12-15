
(set-logic QF_BV)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))
(assert (not (= (bvxnor s t) (bvor (bvand s t) (bvand (bvnot s) (bvnot t))))))
(check-sat)
(exit)
