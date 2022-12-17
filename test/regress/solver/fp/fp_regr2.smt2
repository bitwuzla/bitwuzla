(set-logic QF_FP)
(set-info :status sat)
(declare-const a Float16);
(declare-const b Float16);
(assert (= (fp.abs a) b));
(assert (= (fp.abs a) (fp.abs (fp.neg a))));
(assert (not (and (fp.isNormal (fp.neg a)) (not (fp.isNormal a)))))
(assert (not (and (fp.isSubnormal (fp.neg a)) (not (fp.isSubnormal a)))))
(check-sat)

