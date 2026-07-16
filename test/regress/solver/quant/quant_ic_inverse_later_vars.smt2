(set-info :smt-lib-version 2.6)
(set-logic BV)
; Reduced from SV-COMP/UltimateAutomizer jain_2_true-unreach-call_true-no-overflow.i_198.smt2.
; Refutation requires an inverse instantiation for the first prefix variable
; that references later prefix variables symbolically. Regression for pinning
; referenced later variables to their default ground instantiation instead of
; grounding them with model values (which loses the refutation and diverges
; into value enumeration).
(set-info :status unsat)
(set-option :quant-ic true)
(set-option :quant-ic-underdet true)
(set-option :quant-ic-value-limit 4)
(declare-fun c_main_~x~5 () (_ BitVec 32))
(declare-fun c_main_~y~5 () (_ BitVec 32))
(assert (forall ((v_subst_1 (_ BitVec 32)) (v_subst_2 (_ BitVec 32)) (|main_#t~nondet0| (_ BitVec 32)) (|main_#t~nondet1| (_ BitVec 32))) (or (not (= (bvadd (bvmul (_ bv2 32) v_subst_2) (bvmul (_ bv2 32) |main_#t~nondet0|) c_main_~x~5) (bvadd (bvneg (bvadd c_main_~y~5 (bvmul (_ bv2 32) v_subst_1) (bvmul (_ bv2 32) |main_#t~nondet1|))) (_ bv1 32)))) (= (bvadd c_main_~y~5 (bvmul (_ bv2 32) |main_#t~nondet0|) c_main_~x~5 (bvmul (_ bv2 32) |main_#t~nondet1|) (_ bv4294967295 32)) (_ bv0 32)))))
(assert (not (forall ((|main_#t~nondet0| (_ BitVec 32)) (|main_#t~nondet1| (_ BitVec 32))) (not (= (bvadd (bvmul (_ bv2 32) |main_#t~nondet0|) c_main_~x~5) (bvadd (bvneg (bvadd c_main_~y~5 (bvmul (_ bv2 32) |main_#t~nondet1|))) (_ bv1 32)))))))
(check-sat)
(exit)
