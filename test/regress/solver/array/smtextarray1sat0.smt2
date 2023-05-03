(set-logic QF_AUFBV)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= (select a (_ bv1 1)) (select b (_ bv1 1))))
(assert (not (= a b)))
(check-sat)

