(declare-const x RoundingMode)
(set-info :status sat)
(check-sat-assuming ((fp.eq (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)) (fp ((_ fp.to_sbv 1) x (fp (_ bv0 1) (_ bv0 5) (_ bv0 10))) (_ bv0 15) (_ bv0 112)))))
