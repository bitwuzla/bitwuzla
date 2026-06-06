(set-logic BV)
(set-info :status unsat)
(set-option :quant-ic true)
(set-option :quant-ic-underdet true)
(declare-fun z () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(assert
  (forall ((n0 (_ BitVec 32)) (n2 (_ BitVec 32)) (n1 (_ BitVec 32)))
    (distinct
      (bvadd (bvmul (_ bv2 32) y) (bvmul (_ bv4290772992 32) n0) (bvmul (_ bv4294967292 32) x) (bvmul (_ bv4194304 32) n1) (_ bv1048576 32))
      (bvadd z (bvmul (_ bv4194304 32) n2)))))
(assert
  (not
  (forall ((v3 (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32)) (n0 (_ BitVec 32)) (n2 (_ BitVec 32)) (n1 (_ BitVec 32)))
  (or
    (distinct
      (bvadd (bvmul (_ bv2 32) y) (bvmul (_ bv4194304 32) v1) (bvmul (_ bv4290772992 32) v2) (bvmul (_ bv4290772992 32) n0) (bvmul (_ bv4294967292 32) x) (bvmul (_ bv4194304 32) n1) (_ bv1048576 32))
      (bvadd z (bvmul (_ bv4194304 32) v3) (bvmul (_ bv4194304 32) n2)))
    (=
      (bvadd z (bvmul (_ bv4294967294 32) y) (bvmul (_ bv4194304 32) n0) (bvmul (_ bv4194304 32) n2) (bvmul (_ bv4 32) x) (bvmul (_ bv4290772992 32) n1) (_ bv4293918720 32))
      (_ bv0 32))))))
(check-sat)
(exit)
