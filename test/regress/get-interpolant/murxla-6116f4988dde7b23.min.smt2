; ignore output
(declare-const x (_ BitVec 22))
(set-option :produce-interpolants 1)
(set-option :pp-elim-extracts true)
(assert (bvsgt (_ bv0 38) ((_ sign_extend 16) x)))
(set-info :status sat)
(check-sat)
