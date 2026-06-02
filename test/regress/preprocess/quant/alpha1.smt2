(set-option :pp-quant true)
(set-option :pp-quant-alpha true)
(declare-fun i () Float64)
(assert (and true (forall ((V (_ BitVec 32))) (and (= V (_ bv0 32)) (= (_ bv0 32) (bvadd V (bvmul V V)))))))
(assert (and true (forall ((x (_ BitVec 32))) (and (= x (_ bv0 32)) (= (_ bv0 32) (bvadd x (bvmul x x)))))))
(assert
 (forall ((v_ (_ BitVec 64)))
  (or
   (forall ((v (_ BitVec 32))) (not (bvugt ((_ extract 63 32) v_) (_ bv1073217536 32))))
   (not (= i (fp (_ bv0 1) ((_ extract 62 52) v_) ((_ extract 51 0) v_)))))))
(assert
 (forall ((x (_ BitVec 64)))
  (or
   (forall ((v (_ BitVec 32))) (not (bvugt ((_ extract 63 32) x) (_ bv1073217536 32))))
   (not (= i (fp (_ bv0 1) ((_ extract 62 52) x) ((_ extract 51 0) x)))))))
(assert
 (forall ((x (_ BitVec 64)))
  (or
   (forall ((y (_ BitVec 32))) (not (bvugt ((_ extract 63 32) x) (_ bv1073217536 32))))
   (not (= i (fp (_ bv0 1) ((_ extract 62 52) x) ((_ extract 51 0) x)))))))
(assert
 (forall ((z (_ BitVec 64)))
  (or
   (forall ((y (_ BitVec 32))) (not (bvugt ((_ extract 63 32) z) (_ bv1073217536 32))))
   (not (= i (fp (_ bv0 1) ((_ extract 62 52) z) ((_ extract 51 0) z)))))))
(set-info :status unsat)
(check-sat)
