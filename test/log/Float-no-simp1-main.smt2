(set-logic QF_BVFP)
(set-info :status unsat)

(declare-fun a () Bool)
(assert (let ((a!1 (=> a 
               (= ((_ fp.to_ubv 32)
                    roundTowardZero
                    ((_ to_fp_unsigned 11 53) roundNearestTiesToEven #x00000064))
                  #x00000064))))
  (not (=> true a!1))))

(check-sat)
(exit)
