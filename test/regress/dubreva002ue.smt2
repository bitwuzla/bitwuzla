(set-option :incremental false)
(set-info :source "We reverse an array of length 2 twice in memory at 2 positions.
We show via extensionality that memory has to be equal.

In one case swapping elements is done via XOR in the following way:
x ^= y;
y ^= x;
x ^= y;
In the other case the elements are just swapped.

Contributed by Robert Brummayer (robert.brummayer@gmail.com).")
(set-info :status unsat)
(set-info :category "crafted")
(set-logic QF_AUFBV)
(declare-fun a1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun start1 () (_ BitVec 32))
(declare-fun start2 () (_ BitVec 32))
(assert (let ((_let_0 (select a1 start1))) (let ((_let_1 (select a1 (bvadd start1 (_ bv1 32))))) (let ((_let_2 (store (store a1 (bvadd start1 (_ bv1 32)) _let_0) start1 _let_1))) (let ((_let_3 (bvand (bvnot (bvand (bvnot _let_0) (bvnot _let_1))) (bvnot (bvand _let_0 _let_1))))) (let ((_let_4 (bvand (bvnot (bvand (bvnot _let_1) (bvnot _let_3))) (bvnot (bvand _let_1 _let_3))))) (let ((_let_5 (store (store (store a1 start1 _let_3) (bvadd start1 (_ bv1 32)) _let_4) start1 (bvand (bvnot (bvand (bvnot _let_3) (bvnot _let_4))) (bvnot (bvand _let_3 _let_4)))))) (let ((_let_6 (select _let_5 start2))) (let ((_let_7 (select _let_5 (bvadd (_ bv1 32) start2)))) (let ((_let_8 (bvand (bvnot (bvand (bvnot _let_6) (bvnot _let_7))) (bvnot (bvand _let_6 _let_7))))) (let ((_let_9 (bvand (bvnot (bvand (bvnot _let_7) (bvnot _let_8))) (bvnot (bvand _let_7 _let_8))))) (not (= (bvnot (ite (= (store (store _let_2 (bvadd (_ bv1 32) start2) (select _let_2 start2)) start2 (select _let_2 (bvadd (_ bv1 32) start2))) (store (store (store _let_5 start2 _let_8) (bvadd (_ bv1 32) start2) _let_9) start2 (bvand (bvnot (bvand (bvnot _let_8) (bvnot _let_9))) (bvnot (bvand _let_8 _let_9))))) (_ bv1 1) (_ bv0 1))) (_ bv0 1))))))))))))))
(check-sat)

