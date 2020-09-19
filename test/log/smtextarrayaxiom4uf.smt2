(set-option :incremental false)
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)

