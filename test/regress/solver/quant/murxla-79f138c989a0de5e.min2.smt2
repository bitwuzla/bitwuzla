(set-logic UFBV)
; Narrower variant of murxla-79f138c989a0de5e.min1.smt2 that triggers different
; behavior.
(set-info :status sat)
(set-option :abstraction false)
(set-option :quant-ic true)
(set-option :quant-ic-bounds true)
(declare-const b (_ BitVec 1))
(declare-fun f ((_ BitVec 4) (_ BitVec 4)) (_ BitVec 4))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
  (bvsge (f ((_ zero_extend 3) b) (bvor x (_ bv1 4))) y)))
(check-sat)
(exit)
