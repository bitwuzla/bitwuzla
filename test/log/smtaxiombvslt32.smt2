
(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (let ((_let_0 ((_ extract 31 31) s))) (let ((_let_1 ((_ extract 31 31) t))) (not (= (bvslt s t) (or (and (= _let_0 (_ bv1 1)) (= _let_1 (_ bv0 1))) (and (= _let_0 _let_1) (bvult s t))))))))
(check-sat)
(exit)
