; Regression for an ADC SAT propagator (--adc-sat-propagator=true) soundness
; bug with a PARTIALLY root-fixed watched bit-vector. The first query forces
; v6 into {2,3} (binary 10/11), so the SAT solver fixes v6's MSB to 1 at root
; level while its LSB stays free. In the second query the DISTINCT_N over the
; store indices watches v6; the watched literal must advance past the fixed MSB
; to the free LSB. Otherwise the bit-vector is watched on a fixed literal that
; the SAT solver never (re-)notifies, its assignment collision is missed, and
; the (unsat) query is wrongly reported sat.
(set-logic QF_ABV)
(define-const A (Array (_ BitVec 2) (_ BitVec 4)) ((as const (Array (_ BitVec 2) (_ BitVec 4))) #x0))
(define-const B (Array (_ BitVec 2) (_ BitVec 4)) ((as const (Array (_ BitVec 2) (_ BitVec 4))) #x2))
(define-const C (Array (_ BitVec 2) (_ BitVec 4)) ((as const (Array (_ BitVec 2) (_ BitVec 4))) #x1))
(declare-const v (_ BitVec 2))
(declare-const v6 (_ BitVec 2))
(assert (= A (store (store (store (store C #b00 #x0) #b01 #x0) v #x0) v6 #x0)))
(set-info :status sat)
(check-sat)
(assert (= C (store (store (store (store B v6 #x0) #b00 #x1) #b01 #x1) #b10 #x1)))
(set-info :status unsat)
(check-sat)
