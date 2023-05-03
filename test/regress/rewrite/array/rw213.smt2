(set-info :status unsat)
(set-logic QF_AUFBV)
(declare-fun a2 () (Array (_ BitVec 8) (_ BitVec 16)))
(declare-fun v0 () (_ BitVec 12))
(declare-fun a3 () (Array (_ BitVec 6) (_ BitVec 9)))
(assert (let ((_let_0 (ite (bvule (_ bv1 16) (select a2 (_ bv0 8))) (_ bv1 1) (_ bv0 1)))) (let ((_let_1 (ite (bvsle (select a3 (_ bv0 6)) ((_ sign_extend 8) (ite (bvugt v0 (_ bv0 12)) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (and (not (=> (not (distinct (_ bv1 1) (ite (bvugt v0 (_ bv0 12)) (_ bv1 1) (_ bv0 1)))) (distinct v0 ((_ sign_extend 11) _let_0)))) (not (xor (not (= ((_ sign_extend 5) (_ bv7 3)) ((_ sign_extend 7) (ite (bvugt v0 (_ bv0 12)) (_ bv1 1) (_ bv0 1))))) (=> (not (distinct (_ bv1 1) _let_1)) (= _let_1 _let_0))))))))
(check-sat)

