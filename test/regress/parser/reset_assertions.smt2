(set-logic QF_BV)
(set-option :global-declarations true)
(declare-const x (_ BitVec 3))
(assert (= x #b010))
(set-info :status sat)
(check-sat)
(assert (= x #b001))
(set-info :status unsat)
(check-sat)

(reset-assertions)

(assert (= x #b011))
(set-info :status sat)
(check-sat)
