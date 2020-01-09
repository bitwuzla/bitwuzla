(set-logic QF_FP)
(declare-const a Float16);
(declare-const b Float16);
(assert (= (fp.abs a) b));
(assert (= (fp.abs a) (fp.abs (fp.neg a))));
(assert (not (and (fp.isNormal (fp.neg a)) (not (fp.isNormal a)))))
(assert (not (and (fp.isSubnormal (fp.neg a)) (not (fp.isSubnormal a)))))
(assert (and (fp.isZero (fp.neg a)) (not (fp.isNormal a))))
(assert (not (fp.isInfinite b)))
(assert (not (fp.isNaN b)))
(assert (not (fp.isNegative b)))
(assert (fp.isPositive b))
(assert (and (fp.leq a a) (not (fp.lt a a))))
(assert (not (and (fp.geq (fp.sqrt RNE a) (fp.roundToIntegral RNE b)) (not (fp.gt a b)))))
(check-sat)

