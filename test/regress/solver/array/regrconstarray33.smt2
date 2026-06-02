; Nested constant arrays: model construction picks a default constant array and
; fills indices missing from its coverage. For array-typed (nested) element
; defaults the filled values are arrays compared by node identity, which does
; not capture model equality (a store chain vs. an equivalent constant array),
; so the consistency assertions in construct_model_value must not apply to
; array-typed elements. The constructed model is validated by --check-model.
(set-logic QF_ABV)
(set-info :status sat)
(declare-const O (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1))))
(declare-const o (_ BitVec 2))
(declare-const i (_ BitVec 2))
(assert (= (store O (_ bv0 2) ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv1 1))) (store ((as const (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1)))) ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv1 1))) i (store (store ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv1 1)) (_ bv1 2) (_ bv0 1)) (_ bv0 2) (_ bv0 1)))))
(assert (= (store O (_ bv1 2) (store (store ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv1 1)) (_ bv1 2) (_ bv0 1)) (_ bv0 2) (_ bv0 1))) (store ((as const (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1)))) (store (store ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv0 1)) (_ bv3 2) (_ bv1 1)) i (_ bv1 1))) o ((as const (Array (_ BitVec 2) (_ BitVec 1))) (_ bv1 1)))))
(check-sat)
(exit)
