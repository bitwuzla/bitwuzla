; Regression for a function-solver value bug: a (select ...) with uninterpreted
; element sort has no function model, so FunSolver::value used to fall back to
; the type-wide default value. This conflated the two unrelated selects below,
; causing check() to see equal argument values and emit a spurious function
; congruence lemma whose premise is an equality over the uninterpreted sort.
; Registering that lemma hit the "Equalities over uninterpreted sorts not yet
; supported" path and the solver wrongly answered "unknown". The selects are
; completely unconstrained, so this is trivially sat.
(set-logic QF_AUFBV)
(set-info :status sat)
(declare-sort U 0)
(declare-const a (Array (_ BitVec 2) U))
(declare-const b (Array (_ BitVec 2) U))
(declare-const i (_ BitVec 2))
(declare-const k (_ BitVec 2))
(declare-fun g (U) (_ BitVec 1))
(assert (= (g (select a i)) #b1))
(assert (= (g (select b k)) #b0))
(check-sat)
(exit)
