(set-logic QF_UFBV)
(declare-fun v1 () (_ BitVec 4))
(declare-fun v2 () (_ BitVec 4))
(declare-fun v3 () (_ BitVec 4))
(declare-fun v4 () (_ BitVec 4))
(declare-fun uf5 () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun uf6 () (Array (_ BitVec 4) (_ BitVec 4)))
(assert 
 (not 
  (= v1 v3)))
(assert 
 (= 
  (store uf5 v1 v2) 
  (store uf6 v3 v4)))
(check-sat)
(exit)
