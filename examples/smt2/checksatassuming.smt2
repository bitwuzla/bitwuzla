(set-logic QF_BV)

(declare-fun o0 () (_ BitVec 1))
(declare-fun o1 () (_ BitVec 1))
(declare-fun s0 () (_ BitVec 2))
(declare-fun s1 () (_ BitVec 2))
(declare-fun s2 () (_ BitVec 2))
(declare-fun goal () (_ BitVec 2))

(assert (= s0 (_ bv0 2)))
(assert (= goal (_ bv3 2)))
(check-sat-assuming ((= s0 goal)))

(assert (= s1 (ite (= o0 (_ bv1 1)) (bvadd s0 (_ bv1 2)) s0)))
(check-sat-assuming ((= s1 goal)))

(assert (= s2 (ite (= o1 (_ bv1 1)) (bvadd s1 (_ bv1 2)) s1)))
(check-sat-assuming ((= s2 goal)))

