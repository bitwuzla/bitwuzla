; ignore output
(set-option :produce-interpolants true)
(set-option :interpolants-simp true)
(declare-const x Float64)
(assert (fp.isSubnormal x))
(assert (fp.isNaN x))
(set-info :status unsat)
(check-sat)
(get-interpolants ((fp.isNaN x)))
