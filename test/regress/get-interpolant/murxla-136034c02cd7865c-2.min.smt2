; ignore output
(set-option :produce-interpolants true)
(declare-fun x (Float64) Float64)
(declare-const x5 RoundingMode)
(assert (fp.isInfinite (x (_ +zero 11 53))))
(assert (! (= (bvsaddo (_ bv1 21) ((_ fp.to_sbv 21) x5 (_ -zero 11 53))) (fp.isInfinite (x (_ +zero 11 53)))) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
