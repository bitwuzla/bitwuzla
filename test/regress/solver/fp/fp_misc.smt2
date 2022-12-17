(set-logic QF_FP)
(set-info :status unsat)
(declare-const a Float16);
(declare-const b Float16);
(declare-const rm RoundingMode);
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
(assert (and (fp.geq (fp.sqrt RNE a) (fp.roundToIntegral RNE b)) (not (fp.gt (fp.add RNA a a) b))))
(assert (fp.geq (fp.add RTN a b) (fp.sub RTN a b)))
(assert (fp.leq (fp.mul RTP a (_ +zero 5 11)) (_ -zero 5 11)))
(assert (fp.isNaN (fp.div RTP a (_ +zero 5 11))))
(assert (fp.eq (fp.add rm (fp.mul RTZ a b) a) (fp.fma RTZ a b (fp.rem a b))))
(check-sat)
