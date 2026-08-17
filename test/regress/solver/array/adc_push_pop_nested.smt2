; Coverage for the ADC SAT propagator (--adc-sat-propagator=true) with *nested*
; assertion levels: the DISTINCT_N constraint is registered at level 1, queried
; at level 2, and the levels are popped back down to 0 while the propagator
; that enforces it stays registered in the SAT solver.
;
; (store (store A i x) #b0 y) = B (B a constant array with default #x1) forces
; the two store indices apart, i.e. i = #b1, and forces y = #x1.
(set-logic QF_ABV)
(declare-const i (_ BitVec 1))
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(define-const A (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x0))
(define-const B (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x1))
(push 1)
; Level 1: the DISTINCT_N term is registered here.
(assert (= (store (store A i x) #b0 y) B))
(set-info :status sat)
(check-sat)
(push 1)
; Level 2: contradicts the ADC constraint.
(assert (= i #b0))
(set-info :status unsat)
(check-sat)
(pop 1)
; Back at level 1, satisfiable again.
(set-info :status sat)
(check-sat)
(push 1)
; Level 2: contradicts the element that the ADC constraint leaves over.
(assert (= y #x0))
(set-info :status unsat)
(check-sat)
(pop 1)
(pop 1)
; Level 0: nothing is asserted any more, and the leftover propagators must not
; constrain the (now unconstrained) index i.
(assert (= i #b0))
(set-info :status sat)
(check-sat)
; Re-register the DISTINCT_N above the root-level unit i = #b0.
(push 1)
(assert (= (store (store A i x) #b0 y) B))
(set-info :status unsat)
(check-sat)
(pop 1)
(set-info :status sat)
(check-sat)
