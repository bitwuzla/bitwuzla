(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 8))
(declare-const v1 (_ BitVec 8))
(assert
 (= #b1
  (bvor
   (bvor
    (bvnot
     (ite (= (ite (bvult (bvnot v0) v1) true false) (bvugt v0 (bvnot v1))) #b1 #b0))
    (bvnot (ite (= (bvule (bvnot v0) v1) (bvuge v0 (bvnot v1))) #b1 #b0)))
   (bvor
    (bvnot (ite (= (bvugt (bvnot v0) v1) (bvult v0 (bvnot v1))) #b1 #b0))
    (bvnot (ite (= (bvuge (bvnot v0) v1) (bvule v0 (bvnot v1))) #b1 #b0))))))
(check-sat)
