(declare-fun c () RoundingMode)
(assert (exists ((m Float64)) false))
(assert (fp.geq (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp.add c m (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(check-sat)
