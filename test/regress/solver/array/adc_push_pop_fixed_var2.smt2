; Second regression for the bug described in adc_push_pop_fixed_var.smt2, with
; 2-bit store indices: the DISTINCT_N registered after the pop watches a
; *multi-bit* index whose bits were all root-fixed while unobserved. Before the
; fix, DistinctNPropagator::assigned() saw assignment == 0 for those bits.
(set-logic QF_ABV)
(declare-const i0 (_ BitVec 2))
(declare-const i1 (_ BitVec 2))
(declare-const i2 (_ BitVec 2))
(declare-const i3 (_ BitVec 2))
(declare-const e0 (_ BitVec 2))
(declare-const e1 (_ BitVec 2))
(declare-const e2 (_ BitVec 2))
(define-const C0 (Array (_ BitVec 2) (_ BitVec 2)) ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b10))
(define-const C1 (Array (_ BitVec 2) (_ BitVec 2)) ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00))
(push 1)
(assert (= (select C0 i2) e1))
(assert (= (store (store (store (store C0 i1 e1) i0 e0) i1 e1) i3 e2) C1))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (= (store (store (store (store C1 i3 e0) #b11 e0) i2 e0) i1 #b10) C0))
(set-info :status sat)
(check-sat)
