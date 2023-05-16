(set-logic QF_BV)
(set-option :produce-models false)
(declare-const x (_ BitVec 3))
(assert (= x #b010))
(check-sat) ; expect sat

(reset)

(set-logic QF_ABV)
(set-option :produce-models true)
(declare-const a ( Array (_ BitVec 2) (_ BitVec 3)))
(assert (= x #b011))
(assert (= x (select a #b01)))
(check-sat) ; expect sat
(get-model)
