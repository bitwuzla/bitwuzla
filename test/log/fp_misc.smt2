(set-logic QF_FP)
(declare-const a Float16);
(declare-const b Float16);
(assert (= (fp.abs a) b));
(assert (distinct (fp.abs a) (fp.abs a)));
(check-sat)

