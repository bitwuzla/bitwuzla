; Model construction for function applications that are not registered with the
; function solver: their value is derived from the function model of the applied
; function. Applications whose argument values do not match any recorded
; application fall back to a default value, or, for uninterpreted return sorts,
; to a value unique per application term.
; Values of uninterpreted sorts contain node ids, hence ignore the output.
; ignore output
(set-logic QF_UFBV)
(set-option :produce-models true)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) U)
(declare-fun h ((_ BitVec 4) (_ BitVec 4)) (_ BitVec 4))
(declare-fun k (U) (_ BitVec 4))
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(assert (= (f a) #b0101))
(assert (= (k (g a)) #b0001))
(assert (= (h a a) #b0011))
(assert (distinct a b))
(check-sat)
(get-model)
; None of the applications below occur in the assertions.
(get-value ((f #b1111)))
(get-value ((g b)))
(get-value ((h a b)))
(exit)
