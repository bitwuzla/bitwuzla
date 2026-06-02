; Nested constant arrays (array-typed default element). Default-value
; propagation reaches the base array Ax1 via two store equalities; the inner
; default arrays become model-equal but their constructed model is a non-uniform
; (store-chain) array. Model construction must accept an array-typed default
; element rather than only a value or constant array.
(set-logic QF_ABV)
(set-info :status sat)
(declare-const x0 (Array (_ BitVec 1) (_ BitVec 2)))
(define-fun Ax0 () (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 2))) ((as const (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 2)))) x0))
(declare-const Ax1 (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 2))))
(declare-const x3 (Array (_ BitVec 1) (_ BitVec 2)))
(define-fun Ax3 () (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 2))) ((as const (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 2)))) x3))
(declare-const i0_0 (_ BitVec 2))
(declare-const e0_0 (Array (_ BitVec 1) (_ BitVec 2)))
(declare-const i1_0 (_ BitVec 2))
(declare-const e1_0 (Array (_ BitVec 1) (_ BitVec 2)))
(declare-const i2_0 (_ BitVec 2))
(declare-const e2_0 (Array (_ BitVec 1) (_ BitVec 2)))
(assert (= (store Ax0 i0_0 e0_0) (store Ax1 i1_0 e1_0)))
(assert (= (store Ax1 i2_0 e2_0) Ax3))
(check-sat)
(exit)
