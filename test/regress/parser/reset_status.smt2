(set-info :status sat)
(set-logic QF_BV)
(check-sat)
(reset)
; the status is reset, too
(set-logic QF_BV)
(assert false)
(check-sat)
