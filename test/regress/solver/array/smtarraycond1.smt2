(set-info :status unsat)
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun i () (_ BitVec 32))
(declare-fun c () Bool)
(assert (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))
(check-sat)

