(set-option :incremental false)
(set-info :source "We swap two byte sequences of length 2 twice in memory.
The sequences can not overlap, hence it is always the case
that swapping them twice yields the initial memory.

Swapping is done via XOR in the following way:
x ^= y;
y ^= x;
x ^= y;

Contributed by Robert Brummayer (robert.brummayer@gmail.com).")
(set-info :status unsat)
(set-info :category "crafted")
(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun start1 () (_ BitVec 32))
(declare-fun start2 () (_ BitVec 32))
(assert (let ((_let_0 (select a1 start1))) (let ((_let_1 (select a1 start2))) (let ((_let_2 (bvand (bvnot (bvand (bvnot _let_0) (bvnot _let_1))) (bvnot (bvand _let_0 _let_1))))) (let ((_let_3 (bvand (bvnot (bvand (bvnot _let_1) (bvnot _let_2))) (bvnot (bvand _let_1 _let_2))))) (let ((_let_4 (store (store (store a1 start1 _let_2) start2 _let_3) start1 (bvand (bvnot (bvand (bvnot _let_2) (bvnot _let_3))) (bvnot (bvand _let_2 _let_3)))))) (let ((_let_5 (bvadd start2 (_ bv1 32)))) (let ((_let_6 (select _let_4 (bvadd start1 (_ bv1 32))))) (let ((_let_7 (select _let_4 _let_5))) (let ((_let_8 (bvand (bvnot (bvand (bvnot _let_6) (bvnot _let_7))) (bvnot (bvand _let_6 _let_7))))) (let ((_let_9 (bvand (bvnot (bvand (bvnot _let_7) (bvnot _let_8))) (bvnot (bvand _let_7 _let_8))))) (let ((_let_10 (store (store (store _let_4 (bvadd start1 (_ bv1 32)) _let_8) _let_5 _let_9) (bvadd start1 (_ bv1 32)) (bvand (bvnot (bvand (bvnot _let_8) (bvnot _let_9))) (bvnot (bvand _let_8 _let_9)))))) (let ((_let_11 (select _let_10 start1))) (let ((_let_12 (select _let_10 start2))) (let ((_let_13 (bvand (bvnot (bvand (bvnot _let_11) (bvnot _let_12))) (bvnot (bvand _let_11 _let_12))))) (let ((_let_14 (bvand (bvnot (bvand (bvnot _let_12) (bvnot _let_13))) (bvnot (bvand _let_12 _let_13))))) (let ((_let_15 (store (store (store _let_10 start1 _let_13) start2 _let_14) start1 (bvand (bvnot (bvand (bvnot _let_13) (bvnot _let_14))) (bvnot (bvand _let_13 _let_14)))))) (let ((_let_16 (select _let_15 (bvadd start1 (_ bv1 32))))) (let ((_let_17 (select _let_15 _let_5))) (let ((_let_18 (bvand (bvnot (bvand (bvnot _let_16) (bvnot _let_17))) (bvnot (bvand _let_16 _let_17))))) (let ((_let_19 (bvand (bvnot (bvand (bvnot _let_17) (bvnot _let_18))) (bvnot (bvand _let_17 _let_18))))) (let ((_let_20 (concat (_ bv0 1) (_ bv2 32)))) (let ((_let_21 (bvnot ((_ extract 32 32) (bvadd (concat (_ bv0 1) start1) _let_20))))) (let ((_let_22 (bvnot ((_ extract 32 32) (bvadd _let_20 (concat (_ bv0 1) start2)))))) (not (= (bvand (bvnot (ite (= a1 (store (store (store _let_15 (bvadd start1 (_ bv1 32)) _let_18) _let_5 _let_19) (bvadd start1 (_ bv1 32)) (bvand (bvnot (bvand (bvnot _let_18) (bvnot _let_19))) (bvnot (bvand _let_18 _let_19))))) (_ bv1 1) (_ bv0 1))) (bvnot (bvand (bvnot (bvand _let_22 (bvand (bvnot (ite (bvult start2 (bvadd start1 (_ bv2 32))) (_ bv1 1) (_ bv0 1))) _let_21))) (bvnot (bvand _let_21 (bvand (bvnot (ite (bvult start1 (bvadd start2 (_ bv2 32))) (_ bv1 1) (_ bv0 1))) _let_22)))))) (_ bv0 1)))))))))))))))))))))))))))
(check-sat)

