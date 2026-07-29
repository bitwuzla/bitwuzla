(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(define-fun m () (_ FloatingPoint 11 53) (fp.min x (fp.neg x)))
(assert (fp.lt ((_ to_fp_unsigned 11 53) RNE
                 ((_ fp.to_ubv 1) RNE (fp.mul RNE m m)))
               x))
(set-info :status sat)
(check-sat)
