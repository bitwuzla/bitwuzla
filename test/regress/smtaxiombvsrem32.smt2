
(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (let ((_let_0 ((_ extract 31 31) s))) (let ((_let_1 ((_ extract 31 31) t))) (let ((_let_2 (= _let_0 (_ bv0 1)))) (let ((_let_3 (= _let_1 (_ bv0 1)))) (let ((_let_4 (bvneg s))) (let ((_let_5 (bvneg t))) (not (= (bvsrem s t) (ite (and _let_2 _let_3) (bvurem s t) (ite (and (= _let_0 (_ bv1 1)) _let_3) (bvneg (bvurem _let_4 t)) (ite (and _let_2 (= _let_1 (_ bv1 1))) (bvurem s _let_5) (bvneg (bvurem _let_4 _let_5))))))))))))))
(check-sat)
(exit)
