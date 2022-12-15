
(set-logic QF_BV)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))
(assert (let ((_let_0 ((_ extract 6 6) s))) (let ((_let_1 ((_ extract 6 6) t))) (not (= (bvsle s t) (or (and (= _let_0 (_ bv1 1)) (= _let_1 (_ bv0 1))) (and (= _let_0 _let_1) (bvule s t))))))))
(check-sat)
(exit)
