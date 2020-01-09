(set-logic QF_FP)
(declare-const a Float16);
(declare-const b Float16);
(assert (= (fp.abs a) b));
(assert (fp.isNaN (fp.div RTP a (_ +zero 5 11))))
(check-sat)
