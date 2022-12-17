(set-logic QF_BV)
(set-info :status unsat)
(assert (= #b1 (bvnot (ite (= (concat (ite (= (ite (= #b1 (ite (= #b0 #b1) #b1 #b0)) #b1 #b0) #b1) #b0 #b1) #b0) #b10) #b1 #b0))))
(check-sat)
