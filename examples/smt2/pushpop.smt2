(set-logic QF_BV)

(declare-fun o0 () (_ BitVec 1))
(declare-fun o1 () (_ BitVec 1))
(declare-fun s0 () (_ BitVec 2))
(declare-fun s1 () (_ BitVec 2))
(declare-fun s2 () (_ BitVec 2))
(declare-fun goal () (_ BitVec 2))

(assert (= s0 (_ bv0 2)))
(assert (= goal (_ bv3 2)))
(push 1)
(assert (= s0 goal))
(check-sat)
(pop 1)

(assert (= s1 (ite (= o0 (_ bv1 1)) (bvadd s0 (_ bv1 2)) s0)))
(push 1)
(assert (= s1 goal))
(check-sat)
(pop 1)

(assert (= s2 (ite (= o1 (_ bv1 1)) (bvadd s1 (_ bv1 2)) s1)))
(push 1)
(assert (= s2 goal))
(check-sat)
(pop 1)

