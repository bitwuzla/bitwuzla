; Regression for a soundness bug in the ADC SAT propagator
; (--adc-sat-propagator=true). A DISTINCT_N constraint registered in a later
; solve round watches a constant index whose bits bit-blast to +-true_var,
; which is fixed at root level long before this propagator observes it. CaDiCaL
; never (re-)notifies such fixed assignments, so the constant bit-vector never
; became "fully assigned", its collision was missed, and the ADC constraint was
; silently dropped -> wrong "sat" on the second (unsat) query.
(set-logic QF_ABV)
(declare-const ia (_ BitVec 1))
(declare-const xa (_ BitVec 4))
(declare-const xb (_ BitVec 4))
(define-const A (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x0))
(define-const B (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x1))
(assert (= (store (store A ia xa) #b0 xb) B))
(set-info :status sat)
(check-sat)
(declare-const i2 (_ BitVec 1))
(declare-const y0 (_ BitVec 4))
(declare-const y1 (_ BitVec 4))
(define-const D (Array (_ BitVec 1) (_ BitVec 4)) ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x2))
(assert (= (store (store A i2 y0) #b0 y1) D))
(assert (= y0 #x0))
(set-info :status unsat)
(check-sat)
