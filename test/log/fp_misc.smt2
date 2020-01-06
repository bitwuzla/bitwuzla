(set-logic QF_FP)
(declare-const a Float16);
(declare-const b Float16);
(assert (= (fp.abs a) b));
(assert (= (fp.abs a) (fp.abs (fp.neg a))));
(assert (and (fp.isNormal (fp.neg a)) (not (fp.isNormal a))))
(check-sat)

