(set-info :source "This benchmark generates write chain permutations and tries to show
via extensionality that they are equal.

Contributed by Armin Biere (armin.biere@jku.at).")
(set-info :status sat)
(set-info :category "crafted")
(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun v6 () (_ BitVec 32))
(declare-fun v7 () (_ BitVec 32))
(assert (let ((_let_0 (bvadd (_ bv0 32) v6))) (let ((_let_1 ((_ extract 7 0) v6))) (let ((_let_2 (bvadd (_ bv1 32) v6))) (let ((_let_3 ((_ extract 15 8) v6))) (let ((_let_4 (bvadd (_ bv2 32) v6))) (let ((_let_5 ((_ extract 23 16) v6))) (let ((_let_6 (bvadd (_ bv3 32) v6))) (let ((_let_7 ((_ extract 31 24) v6))) (let ((_let_8 (bvadd (_ bv0 32) v7))) (let ((_let_9 ((_ extract 7 0) v7))) (let ((_let_10 (bvadd (_ bv1 32) v7))) (let ((_let_11 ((_ extract 15 8) v7))) (let ((_let_12 (bvadd (_ bv2 32) v7))) (let ((_let_13 ((_ extract 23 16) v7))) (let ((_let_14 (bvadd (_ bv3 32) v7))) (let ((_let_15 ((_ extract 31 24) v7))) (not (= (bvnot (ite (= (store (store (store (store (store (store (store (store a1 _let_0 _let_1) _let_2 _let_3) _let_4 _let_5) _let_6 _let_7) _let_8 _let_9) _let_10 _let_11) _let_12 _let_13) _let_14 _let_15) (store (store (store (store (store (store (store (store a1 _let_8 _let_9) _let_10 _let_11) _let_12 _let_13) _let_14 _let_15) _let_0 _let_1) _let_2 _let_3) _let_4 _let_5) _let_6 _let_7)) (_ bv1 1) (_ bv0 1))) (_ bv0 1))))))))))))))))))))
(check-sat)

