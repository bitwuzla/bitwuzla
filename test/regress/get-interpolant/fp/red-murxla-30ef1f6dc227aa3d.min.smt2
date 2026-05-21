; ignore output
(declare-const x Float128)
(set-option :produce-interpolants true)
(assert true)
(assert (! (fp.lt x (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)) (fp.max x (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)))) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolants (a1))
