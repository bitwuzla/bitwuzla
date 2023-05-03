(set-info :status unsat)
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun i () (_ BitVec 1))
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)

