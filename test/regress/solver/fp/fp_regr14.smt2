(set-info :status sat)
(declare-fun c () RoundingMode)
(declare-fun c_ () Float32)
(assert (= c_ ((_ to_fp 8 24) c (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(check-sat)