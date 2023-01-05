(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 8))
(declare-const v1 (_ BitVec 8))
(assert
 (= #b1
  (bvor
   (bvor
    (bvnot
     (ite
      (=
       (ite (bvult v0 v1) #b1 #b0)
       ((_ extract 7 7) (bvor (bvand (bvnot v0) v1) (bvand (bvxnor v0 v1) (bvsub v0 v1)))))
      #b1 #b0))
    (bvnot
     (ite
      (=
       (ite (bvult v0 v1) #b1 #b0)
       ((_ extract 7 7) (bvor (bvand (bvnot v0) v1) (bvand (bvor (bvnot v0) v1) (bvsub v0 v1)))))
     #b1 #b0)))
   (bvnot
    (ite
     (=
      (ite (bvule v0 v1) #b1 #b0)
      ((_ extract 7 7) (bvand (bvor (bvnot v0) v1) (bvor (bvxor v0 v1) (bvnot (bvsub v1 v0))))))
     #b1 #b0)))))
(check-sat)
