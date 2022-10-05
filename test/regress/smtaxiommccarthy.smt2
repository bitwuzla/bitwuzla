(set-option :incremental false)
(set-logic QF_AUFBV)
(declare-fun i () (_ BitVec 32))
(declare-fun j () (_ BitVec 32))
(declare-fun v () (_ BitVec 8))
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (select (store a i v) j) (ite (= i j) v (select a j)))))
(check-sat)

