(set-logic QF_BVFP)
(set-info :status sat)
(declare-fun _substvar_179_ () (_ FloatingPoint 8 24))
(declare-fun v_115$$1 () Bool)
(assert (= (_ +zero 8 24) (ite v_115$$1 _substvar_179_ (_ +zero 8 24))))
(check-sat)

