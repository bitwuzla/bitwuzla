(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 3))
(assert (= x #b010))
(check-sat) ; expect sat
(assert (= x #b001))
(check-sat) ; expect unsat

(reset-assertions)

(assert (= x #b011))
(check-sat) ; expect sat
(get-model)
