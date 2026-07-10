; Boolean option values passed via (set-option ...) are normalized
; case-insensitively (see bzla::option::Options::set). Enabling model
; production with the upper-case value TRUE must be accepted; otherwise
; (get-value ...) below would fail with "model generation is not enabled".
(set-logic QF_BV)
(set-option :produce-models TRUE)
(declare-const x (_ BitVec 4))
(assert (= x #b0001))
(check-sat)
(get-value (x))
(exit)
