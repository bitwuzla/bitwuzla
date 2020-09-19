
(set-logic QF_BV)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (let ((_let_0 (bvurem (ite (= ((_ extract 31 31) s) (_ bv1 1)) (bvneg s) s) (ite (= ((_ extract 31 31) t) (_ bv1 1)) (bvneg t) t)))) (let ((_let_1 (= _let_0 (_ bv0 32)))) (let ((_let_2 (= ((_ extract 31 31) s) (_ bv0 1)))) (let ((_let_3 (= ((_ extract 31 31) t) (_ bv0 1)))) (let ((_let_4 (bvneg _let_0))) (not (= (bvsmod s t) (ite (and _let_2 _let_3) _let_0 (ite (and (= ((_ extract 31 31) s) (_ bv1 1)) _let_3) (ite _let_1 (_ bv0 32) (bvadd _let_4 t)) (ite (and _let_2 (= ((_ extract 31 31) t) (_ bv1 1))) (ite _let_1 (_ bv0 32) (bvadd _let_0 t)) _let_4)))))))))))
(check-sat)
(exit)
