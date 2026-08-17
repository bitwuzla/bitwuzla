; Regression for a soundness bug in the ADC SAT propagator
; (--adc-sat-propagator=true) that only shows up incrementally: a
; DistinctNPropagator registered *after* a pop watches a bit that CaDiCaL had
; already root-fixed while nobody was observing it. Propagator::watch() skipped
; its fixed() query in that case, leaving assignment = 0, so the propagator
; registered the store index under a bogus all-zero value, dropped the ADC
; constraint and answered the second (unsat) query "sat".
(set-logic QF_ABV)
(declare-const i1 (_ BitVec 1))
(declare-const e0 (_ BitVec 3))
(declare-const e1 (_ BitVec 3))
(declare-const e2 (_ BitVec 3))
(define-const C0 (Array (_ BitVec 1) (_ BitVec 3)) ((as const (Array (_ BitVec 1) (_ BitVec 3))) #b000))
(define-const C1 (Array (_ BitVec 1) (_ BitVec 3)) ((as const (Array (_ BitVec 1) (_ BitVec 3))) #b101))
(push 1)
; Both stores use the same index, so they cannot cover both indices of C1:
; unsatisfiable, and the query root-fixes bits that are not observed yet.
(assert (= (store (store C1 i1 e0) i1 e0) C0))
(assert (= e0 #b111))
(set-info :status unsat)
(check-sat)
(pop 1)
; A fresh DISTINCT_N over (i1, #b1) is registered here, i.e. after the pop.
; #b1 forces e2 = #b101 and i1 = #b0 forces e1 = #b101, contradicting e1 != e2.
(assert (= (store (store C1 i1 e1) #b1 e2) C0))
(assert (not (= e1 e2)))
(set-info :status unsat)
(check-sat)
