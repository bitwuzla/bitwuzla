; ignore output
(set-option :rewrite-level 0)
(set-option :produce-interpolants true)
(declare-const x RoundingMode)
(assert (= RTN x))
(assert (! (distinct x RTN) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolants (a1))
