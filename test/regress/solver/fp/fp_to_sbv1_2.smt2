(set-option :produce-models true)
(set-info :status sat)
(check-sat)
(get-value ((and (bvusubo (_ bv0 1) (_ bv1 1)) (bvusubo ((_ fp.to_sbv 1) roundTowardNegative (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))) (_ bv1 1)))))
