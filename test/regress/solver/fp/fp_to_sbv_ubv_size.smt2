(set-logic QF_BVFP)
(set-info :status sat)
(declare-const rm RoundingMode)
(declare-const x (_ FloatingPoint 5 11))
; The index of fp.to_sbv/fp.to_ubv determines the size of the resulting
; bit-vector and is thus not bounded by the maximum supported floating-point
; exponent size.
(assert (= ((_ fp.to_sbv 89) rm x) ((_ fp.to_sbv 89) rm x)))
(assert (= ((_ fp.to_ubv 64) rm x) ((_ fp.to_ubv 64) rm x)))
(check-sat)
