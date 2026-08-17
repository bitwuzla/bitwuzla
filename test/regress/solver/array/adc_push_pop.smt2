; Coverage for the ADC SAT propagator (--adc-sat-propagator=true) combined with
; incremental push/pop. Every query below is decided by the DISTINCT_N
; constraint: (store (store A i x) #b0 y) can only be equal to the constant
; array B (default value #x1) if the two store indices are distinct, i.e. if
; i = #b1.
;
; DISTINCT_N terms are registered through a backtrackable cache, but the
; DistinctNPropagator registered for them is never unregistered on pop, so each
; push/pop cycle adds another propagator for the very same constraint. This
; test pins down that the duplicates stay sound and that an assertion from a
; popped level cannot leak into a later query through them.
(set-logic QF_ABV)
(declare-const i (_ BitVec 1))
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(define-const A (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x0))
(define-const B (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x1))
; Level 1: satisfiable, needs i != #b0.
(push 1)
(assert (= (store (store A i x) #b0 y) B))
(set-info :status sat)
(check-sat)
(pop 1)
; Same assertion again after the pop, so the same DISTINCT_N term is registered
; a second time. i = #b0 now contradicts the ADC constraint.
(push 1)
(assert (= (store (store A i x) #b0 y) B))
(assert (= i #b0))
(set-info :status unsat)
(check-sat)
(pop 1)
; The popped (= i #b0) must not survive: satisfiable again.
(push 1)
(assert (= (store (store A i x) #b0 y) B))
(set-info :status sat)
(check-sat)
(pop 1)
; Now assert i = #b0 at level 0 (a root-level unit) and re-register the
; DISTINCT_N above it.
(assert (= i #b0))
(push 1)
(assert (= (store (store A i x) #b0 y) B))
(set-info :status unsat)
(check-sat)
(pop 1)
; Only i = #b0 is left. Stale propagators from the popped levels must not
; force the store indices apart.
(set-info :status sat)
(check-sat)
