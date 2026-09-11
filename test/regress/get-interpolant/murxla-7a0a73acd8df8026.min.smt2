; ignore output
(set-option :produce-interpolants true)
(set-option :interpolants-simp true)
(assert true)
(assert (forall ((x1 Bool) (x2 Bool) (x3 Bool)) false))
(set-info :status unsat)
(check-sat)
(get-interpolants (true))
