; ignore output
(set-option :produce-interpolants true)
(set-option :rewrite-level 0)
(declare-const x (_ BitVec 64))
(assert (! (bvuaddo x (_ bv1 64)) :named a1))
(assert (fp.isSubnormal (fp.fma RTZ (_ +zero 11 53) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(set-info :status unsat)
(check-sat)
(get-interpolants (a1))
