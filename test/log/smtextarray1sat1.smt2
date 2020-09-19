(set-option :incremental false)
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= (select a (_ bv0 1)) (select b (_ bv0 1))))
(assert (not (= a b)))
(check-sat)

