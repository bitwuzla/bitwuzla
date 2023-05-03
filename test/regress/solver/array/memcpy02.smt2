(set-info :source "We verify the correctness of the memcpy algorithm.
We represent main memory as byte array of size 2 ^ 32,
and model the memcpy algorithm with pointer arithmetic.
We assume that the memory locations do not overlap.
Length: 2

Contributed by Armin Biere (armin.biere@jku.at).")
(set-info :status unsat)
(set-info :category "crafted")
(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun src () (_ BitVec 32))
(declare-fun dst () (_ BitVec 32))
(declare-fun j () (_ BitVec 32))
(assert (let ((_let_0 (bvadd src (_ bv2 32)))) (let ((_let_1 (bvadd dst (_ bv2 32)))) (let ((_let_2 (store a1 dst (select a1 src)))) (not (= (bvand (bvand (bvand (bvand (bvnot (ite (bvult _let_0 src) (_ bv1 1) (_ bv0 1))) (bvnot (ite (bvult _let_1 dst) (_ bv1 1) (_ bv0 1)))) (bvnot (bvand (ite (bvult dst _let_0) (_ bv1 1) (_ bv0 1)) (ite (bvult src _let_1) (_ bv1 1) (_ bv0 1))))) (ite (bvult j (_ bv2 32)) (_ bv1 1) (_ bv0 1))) (bvnot (ite (= (select a1 (bvadd src j)) (select (store _let_2 (bvadd dst (_ bv1 32)) (select _let_2 (bvadd src (_ bv1 32)))) (bvadd dst j))) (_ bv1 1) (_ bv0 1)))) (_ bv0 1)))))))
(check-sat)

