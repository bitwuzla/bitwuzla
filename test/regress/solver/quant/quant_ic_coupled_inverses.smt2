(set-info :smt-lib-version 2.6)
(set-logic BV)
; Exercises the triangular closure of coupled inverse instantiations in a
; single lemma: x1's inverse is conditional (shift-amount IC) and references
; x2, x2's inverse is exact (bvadd, under-determined extract) and references
; x1. The refutation is forced in one round: x2's definition makes x1's
; shift IC valid under the forward-closed condition, which pins the literal
; true at the instantiation point, contradicting the instantiation. The
; variables are 64-bit (under 32-bit extracts) so that their default
; instantiations are always values and the inverse computation is triggered
; for both. Under dependency-pinning stratification this takes one round and
; one (escapable) lemma more; under the pre-stratification code the coupled
; conditions were the cyclic-system soundness hazard.
(set-info :status unsat)
(set-option :quant-ic true)
(set-option :quant-ic-underdet true)
(set-option :quant-ic-value-limit 0)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (forall ((x1 (_ BitVec 64)) (x2 (_ BitVec 64)))
  (not (= (bvadd (bvshl s ((_ extract 31 0) x1)) ((_ extract 31 0) x2)) t))))
(check-sat)
(exit)
