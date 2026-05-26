(set-logic QF_FP)
(assert (= (_ -oo 2 3) (fp #b1 #b11 #b00)))
(set-info :status sat)
(check-sat)
