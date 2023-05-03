(set-info :status unsat)
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 4)))
(define-fun b0 () Bool (= (select a (_ bv0 4)) (select b (_ bv0 4))))
(define-fun b1 () Bool (= (select a (_ bv1 4)) (select b (_ bv1 4))))
(define-fun b2 () Bool (= (select a (_ bv2 4)) (select b (_ bv2 4))))
(define-fun b3 () Bool (= (select a (_ bv3 4)) (select b (_ bv3 4))))
(define-fun b4 () Bool (= (select a (_ bv4 4)) (select b (_ bv4 4))))
(define-fun b5 () Bool (= (select a (_ bv5 4)) (select b (_ bv5 4))))
(define-fun b6 () Bool (= (select a (_ bv6 4)) (select b (_ bv6 4))))
(define-fun b7 () Bool (= (select a (_ bv7 4)) (select b (_ bv7 4))))
(define-fun b8 () Bool (= (select a (_ bv8 4)) (select b (_ bv8 4))))
(define-fun b9 () Bool (= (select a (_ bv9 4)) (select b (_ bv9 4))))
(assert (! (= (select a (_ bv10 4)) (select b (_ bv10 4))) :named a0))
(assert (! (= (select a (_ bv11 4)) (select b (_ bv11 4))) :named a1))
(assert (! (= (select a (_ bv12 4)) (select b (_ bv12 4))) :named a2))
(assert (! (= (select a (_ bv13 4)) (select b (_ bv13 4))) :named a3))
(assert (! (= (select a (_ bv14 4)) (select b (_ bv14 4))) :named a4))
(assert (! (= (select a (_ bv15 4)) (select b (_ bv15 4))) :named a5))
(assert (! (not (= a b)) :named a6))
(check-sat-assuming (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9))
(get-unsat-core)
(get-unsat-assumptions)