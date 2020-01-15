(set-logic QF_BVFP)
(set-info :status unsat)

(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (= (fp.div roundNearestTiesToEven
           (fp #b0 #x80 #b00000000000000000000000)
           (fp #b0 #x81 #b10000000000000000000000))
           a))
(assert (= (fp.mul roundNearestTiesToEven
           a
           (fp #b0 #x81 #b10000000000000000000000))
           b))
(assert (= (= ((_ fp.to_sbv 32) roundTowardZero b) #x00000002) c))
(assert (let ((a!1 (=> true (=> d (=> (not c) false))))) (not a!1)))

(check-sat)
(exit)
