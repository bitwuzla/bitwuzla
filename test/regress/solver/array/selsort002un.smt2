(set-option :incremental false)
(set-info :source "We verify that selection sort sorts an array
of length 2 in memory. Additionally, we read an element
at an arbitrary index of the initial array and show that this
element can not be unequal to an element in the sorted array.

Contributed by Robert Brummayer (robert.brummayer@gmail.com).")
(set-info :status unsat)
(set-info :category "crafted")
(set-logic QF_AUFBV)
(declare-fun a2 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun start () (_ BitVec 32))
(declare-fun index () (_ BitVec 32))
(assert (let ((_let_0 (select a2 index))) (let ((_let_1 (select a2 start))) (let ((_let_2 (bvadd (_ bv1 32) start))) (let ((_let_3 (ite (= (_ bv1 1) (ite (bvult (select a2 _let_2) _let_1) (_ bv1 1) (_ bv0 1))) _let_2 start))) (let ((_let_4 (store (store a2 start (select a2 _let_3)) _let_3 _let_1))) (let ((_let_5 (select _let_4 start))) (let ((_let_6 (select _let_4 _let_2))) (not (= (bvnot (bvand (bvand (_ bv1 1) (bvnot (ite (bvult _let_6 _let_5) (_ bv1 1) (_ bv0 1)))) (bvnot (bvand (bvand (bvnot (ite (bvult index start) (_ bv1 1) (_ bv0 1))) (ite (bvult index (bvadd start (_ bv2 32))) (_ bv1 1) (_ bv0 1))) (bvand (bvand (_ bv1 1) (bvnot (ite (= _let_0 _let_5) (_ bv1 1) (_ bv0 1)))) (bvnot (ite (= _let_0 _let_6) (_ bv1 1) (_ bv0 1)))))))) (_ bv0 1)))))))))))
(check-sat)

