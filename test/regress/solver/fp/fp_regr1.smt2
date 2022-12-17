(set-logic QF_FP)
(set-info :status sat)
(declare-const a Float16);
(declare-const b Float16);
(assert (not (and (fp.isNormal (fp.neg a)) (not (fp.isNormal a)))))
(check-sat)

