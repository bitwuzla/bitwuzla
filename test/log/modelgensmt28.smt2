(set-logic QF_UFBV)
(declare-fun uf1 () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun uf2 () (Array (_ BitVec 1) (_ BitVec 1)))
(assert 
 (select uf1 #b1))
(assert 
 (select uf1 #b0))
(assert 
 (not 
  (= uf1 uf2)))
(assert 
 (select uf2 #b0))
(check-sat)
(exit)
