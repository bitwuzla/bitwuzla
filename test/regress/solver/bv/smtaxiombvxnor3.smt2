
(set-logic QF_BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(assert (not (= (bvxnor s t) (bvor (bvand s t) (bvand (bvnot s) (bvnot t))))))
(check-sat)
(exit)
