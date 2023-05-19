(set-info :status unsat)
(declare-const __ (_ BitVec 2))
(assert
 (bvule
  (bvmul
   ((_ zero_extend 30) __)
   (_ bv4 32)
   ((_ zero_extend 30) __)
   (_ bv4 32))
  (_ bv119 32)))
(assert
 (not
  (bvult
   (bvadd
    (_ bv1 32)
    (bvmul
     ((_ zero_extend 30) __)
     (_ bv4 32)
     ((_ zero_extend 30) __) (_ bv4 32))) (_ bv128 32))))
(check-sat)
