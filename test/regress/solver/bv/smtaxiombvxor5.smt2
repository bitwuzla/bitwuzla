
(set-logic QF_BV)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(assert (not (= (bvxor s t) (bvor (bvand s (bvnot t)) (bvand (bvnot s) t)))))
(check-sat)
(exit)
