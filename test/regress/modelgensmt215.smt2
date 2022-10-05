(set-logic QF_UFBV)
(declare-fun v1 () (_ BitVec 1))
(declare-fun v2 () (_ BitVec 1))
(declare-fun uf3 () (Array (_ BitVec 2) (_ BitVec 4)))
(define-fun $e4 () Bool 
 (= uf3 
  (store uf3 
   (bvnot 
    (concat #b0 
     (bvnot v1))) #b1111)))
(assert 
 (not 
  (= 
   (bvnot 
    (ite $e4 #b1 #b0)) 
   (bvnot v2))))
(assert $e4)
(assert (distinct v1 #b0))
(check-sat)
(exit)
